/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Level.Types

/-!
# Basic level constructions and functions
-/

public section

namespace LilLean

variable {ℓ : Type}

def Level.hashAddOffset (h : UInt64) (offset : Nat) : UInt64 :=
  h + (offset.toUInt64 <<< 2)

/--
Standard hash computation for levels, given a function `getHash` that returns
hashes for levels within `u`.

Lowest two bits encode hasParam (bit 0) and hasMVar (bit 1).
The hash of `Level.zero` is `0`.

Offsets are incorporated in a simple way.
-/
def Level.hashCore (u : Level ℓ) (offset : Nat)
    (getHash : ℓ → UInt64) : UInt64 :=
  let mkHash (mixed : UInt64) (bits : UInt64) : UInt64 :=
    hashAddOffset ((mixed &&& ~~~3) ||| (bits &&& 3)) offset
  match u with
  | .zero => 0
  | .succ v =>
    let hv := getHash v
    hashAddOffset hv (offset + 1)
  | .max v w =>
    let hv := getHash v
    let hw := getHash w
    mkHash (mixHash 4 <| mixHash hv hw) (hv ||| hw)
  | .ipos v w =>
    let hv := getHash v
    let hw := getHash w
    mkHash (mixHash 5 <| mixHash hv hw) (hv ||| hw)
  | .param n =>
    let hn := hash n
    mkHash (mixHash 6 hn) 1
  | .mvar mvarId =>
    let hm := hash mvarId
    mkHash (mixHash 7 hm) 2

def Level.isZero : Level ℓ → Bool
  | .zero => true
  | _ => false

section
variable {m : Type → Type} [Monad m]

section
variable [MonadGetLevel m ℓ]

def isLevelZero (u : ℓ) : m Bool :=
  return (← getLevel u).isZero

/--
Returns `true` if `u` is zero, no matter the assignments to metavariables
or parameters.
-/
partial def isLevelAlwaysZero (u : ℓ) : m Bool := do
  match ← getLevel u with
  | .zero => return true
  | .succ _ => return false
  | .mvar _ => return false
  | .param _ => return false
  | .ipos v w => isLevelAlwaysZero v <||> isLevelAlwaysZero w
  | .max v w => isLevelAlwaysZero v <&&> isLevelAlwaysZero w

/--
Returns `true` if `u` is never zero, no matter the assignments to metavariables
or parameters.
-/
partial def isLevelNeverZero (u : ℓ) : m Bool := do
  match ← getLevel u with
  | .zero => return false
  | .succ _ => return true
  | .mvar _ => return false
  | .param _ => return false
  | .ipos v w => isLevelNeverZero v <&&> isLevelNeverZero w
  | .max v w => isLevelNeverZero v <||> isLevelNeverZero w

/--
Returns `true` if `u` and `v` are structurally equal.
-/
partial def levelEq [BEq ℓ] (u v : ℓ) : m Bool := do
  let (u', uOffset) ← getLevelOffset u
  let (v', vOffset) ← getLevelOffset v
  if uOffset != vOffset then
    return false
  if u' == v' then
    return true
  if (← levelHash u') != (← levelHash v') then
    return false
  match (← getLevel u'), (← getLevel v') with
  | .zero, .zero => return true
  | .mvar uMVarId, .mvar vMVarId => return uMVarId == vMVarId
  | .param un, .param vn => return un == vn
  | .ipos ua ub, .ipos va vb => levelEq ua va <&&> levelEq ub vb
  | .max ua ub, .max va vb => levelEq ua va <&&> levelEq ub vb
  | _, _ => return false

end

section
variable [MonadMkLevel m ℓ]

/-- Makes `Level.zero + n`. -/
def mkLevelConst (n : Nat) : m ℓ := do
  mkLevelOffset (← mkLevelZero) n

/-- Makes `imax u v`, which is zero if `v = 0` and otherwise `max u v`. -/
def mkLevelIMax (u v : ℓ) : m ℓ := do
  mkLevelMax (← mkLevelIPos u v) v

section Update
variable [MonadGetLevel m ℓ] [BEq ℓ]

/-- Does `mkLevelSucc newU`, but returns `orig` if possible. -/
def updateLevelSucc (orig newU : ℓ) : m ℓ := do
  if let .succ u ← getLevel orig then
    if u == newU then
      return orig
  mkLevelSucc newU

/-- Does `mkLevelOffset newU newOffset`, but returns `orig` if possible. -/
def updateLevelOffset (orig newU : ℓ) (newOffset : Nat) : m ℓ := do
  let (u, offset) ← getLevelOffset orig
  if offset == newOffset && u == newU then
    return orig
  mkLevelOffset newU newOffset

/-- Does `mkLevelMax' newU newV`, but returns `orig` if possible. -/
def updateLevelMax (orig newU newV : ℓ) : m ℓ := do
  if let .max u v ← getLevel orig then
    if u == newU && v == newV then
      return orig
  mkLevelMax newU newV

/-- Does `mkLevelIPos newU newV`, but returns `orig` if possible. -/
def updateLevelIPos (orig newU newV : ℓ) : m ℓ := do
  if let .ipos u v ← getLevel orig then
    if u == newU && v == newV then
      return orig
  mkLevelIPos newU newV

end Update

section
variable [MonadGetLevel m ℓ] [BEq ℓ]

/--
Like `mkLevelMax u v`, but returns `u` or `v` if simple checks detect that
one subsumes the other.
-/
partial def mkLevelMax' [BEq ℓ] (u v : ℓ) : m ℓ := do
  if u == v then
    return u
  if (← isLevelZero u) then
    return v
  if (← isLevelZero v) then
    return u
  let (u', uOffset) ← MonadGetLevel.getLevelOffset u
  let (v', vOffset) ← MonadGetLevel.getLevelOffset v
  if ← levelEq u' v' then
    return if uOffset ≥ vOffset then u else v
  if (← isLevelZero u') && uOffset ≤ vOffset then
    return v
  if (← isLevelZero v') && uOffset ≥ vOffset then
    return u
  mkLevelMax u v

/--
Like `mkLevelIPos u v`, but returns `0` or `u` if simple checks detect
the expression can be simplified.
-/
partial def mkLevelIPos' [BEq ℓ] (u v : ℓ) : m ℓ := do
  if u == v then
    return u
  if (← isLevelZero u <||> isLevelZero v) then
    return ← mkLevelZero
  if (← isLevelNeverZero v) then
    return u
  mkLevelIPos u v

end

end

section Normalize
/-!
## Level normalization

We say two level expressions are *equivalent* if all concrete assignments to
level parameters and level metavariables yield the same concrete universe level.
For simplicity of discussion, let's call both parameters and metavariables
*variables*.

To prove two level expressions are equivalent, we can put the expressions into
normal form and check equality. We could get away with a mere simplification
routine if it handles common cases --- in Lean 4, expressions with `imax` do
are merely simplified, not normalized --- but in LilLean opt for a complete
normalization routine.

For levels without any impredicativity handling (i.e., those without `ipos`),
normal forms are straightforward. Given level expressions `u,v,w` and concrete
levels `c,d` ("concrete" means a successor of zero), we have the following
rewrite rules:
- `max u 0 = u`
- `max 0 u = u`
- `max (max u v) w = max u (max v w)` (and we write `max u v w` for the latter)
- `max u v = max v u` (for sorting)
- `(max u v) + c = max (u + c) (v + c)`
- `max c (u + d) = u + d` if `c ≤ d`
- `max (u + c) (u + d) = u + d` if `c ≤ d`
By rewriting with these, we can put level expressions into the form
`max (a₁ + c₁) (a₂ + c₂) ... (aₙ + cₙ)` where each `aᵢ` is either `0` or
a variable, only `aₙ` can be `0` (and if it is, then `cₙ > cᵢ` for all `i < n`),
each variable appears at most once, and the terms are sorted by variable name.
The constant offsets do not play a role in the order.

Handling `ipos` expressions complicates things. First, recall that
`ipos u 0 = 0` and `ipos u v = u` if `v > 0`, so testing whether a given
level is always zero or never zero can be used to simplify an `ipos`
expression. These tests are represented by `isLevelAlwaysZero` and
`isLevelNeverZero`; we reproduce the main rules here:
- `u+(c+1) = 0` is false
- `u+(c+1) > 0` is true
- `max u v = 0` iff `u = 0` and `v = 0`
- `max u v > 0` iff `u > 0` or `v > 0`
- `ipos u v = 0` iff `u = 0` or `v = 0`
- `ipos u v > 0` iff `u > 0` and `v > 0`
If we know whether each variable is zero or positive, these are sufficient
to simplify `ipos` expressions

An interesting property of `ipos` is that it is associative
(`ipos u (ipos v w) = ipos (ipos u v) w`), which justifies writing
`ipos u v w` for `ipos u (ipos v w)`. We can think of this `ipos v w` acting as
a conjunction, since this is `if v > 0 and w > 0 then u else 0`, and so in
`ipos u v w` we can read it as "if both `v` and `w` are nonzero then it's `u`,
otherwise it's `0`". Furthermore, any `ipos` appearing in the second argument of
an `ipos` is commutative (`ipos u (ipos v w) = ipos u (ipos w v)`), which allows
everything after the first argument to be sorted.
Additional rules:
- `ipos u (max v₁ v₂) = max (ipos u v₁) (ipos u v₂)`
- `ipos (max u₁ u₂) v = max (ipos u₁ v) (ipos u₂ v)`
- `(ipos u v) + c = max c (ipos (u + c) v)`
- `ipos u u = u`
- `max (ipos (u + c) (ipos v w)) (ipos (u + d) v) = ipos (u + d)` if `c ≤ d`
So, by rewriting we can put any given level expression into the form
where it is a `max` of `ipos (aᵢ + cᵢ) (ipos ...vsᵢ...)` terms, where
`vsᵢ` is a list of variables. If `aᵢ` is a variable, then we may assume it is
not in `vsᵢ`, by the `ipos u u = u` rule. The final rule in the list above
allows us to eliminate terms that are implied by others. By eliminating them,
then making obvious simplifications, and then sorting them, we obtain a normal
form.

The key idea for why this gives a normal form is that, if there are `n`
variables `v₁,...,vₙ`, we can imagine simplifying the level under all possible
choices of additional hypotheses of each variable being either zero or positive.
This gives an indexed family of `2ⁿ` level expressions that can be simplified
and then normalized into forms not containing `ipos` expressions.
Theoretically, we could test these `Set Variable → Level` functions for
equality, which is exactly testing level equivalence.

So, we can encode these `f : Set Variable -> Level` functions by taking
`max_{vs : Set Variable} ipos (f vs) (ipos ...vs...)`, which we can simplify
according to the above rules. We do not prove uniqueness of normal forms here.
(The concepts I have in mind for proving it are (1) the "`u`-content" of a
level expression, where `u` is zero or a variable, (2) that knowing `u`-content
for all `u` determines a level, and (3) that the `ipos ...vs...` "coefficients"
after simplification are a basis for a positive cone in the boolean algebra
`Set Variable`.)

Comment about `ipos`: Lean 4 only has `imax`, and it does not really attempt
to normalize level expressions containing them, beyond recursively normalizing
the arguments and simplifying if possible. With LilLean's `ipos`, we have clear
normal forms even for impredicative level expressions. However, sort
polymorphism seems to be relatively rare in practice, and it should be said that
Lean's normalization failures do not seem to cause issues.

Example of impredicativity: `α : Type u`, `β : Type v`, `γ : Sort w`.
Then `α → β → γ : imax (u + 1) (imax (v + 1) w)`, and
```
imax (u + 1) (imax (v + 1) w)
  = imax (u + 1) (max (ipos (v + 1) w) w)
  = max (ipos (u + 1) (max (ipos (v + 1) w) w)) (ipos (v + 1) w) w
  = max (ipos (u + 1) w) (ipos (v + 1) w) w
```
This is the normal form, assuming `u` comes before `v` comes before `w` in the
total order on universe level parameters.
-/

variable [MonadGetLevel m ℓ]

/--
Folds over all components of a `max` level expression while distributing
offsets. Calls `f` with each `u'+offset` pair. The level `u'` is zero, a
parameter, a metavariable, or an `ipos` expression.

For example, `max ((max u v) + 2) w` will call `f` on `u+2`, `v+2`, and `f w`.
-/
partial def foldLevelMaxM {α : Type} (u : ℓ)
    (f : α → ℓ → Nat → m α) (init : α) (offset : Nat := 0) :
    m α :=
  go u offset init
where
  go (u : ℓ) (offset : Nat) (init : α) : m α := do
    let (u', uOffset) ← getLevelOffset u
    let offset' := offset + uOffset
    match ← getLevel u' with
    | .max v w => go w offset' (← go v offset' init)
    | _ => f init u' offset'

inductive LevelBase (ℓ : Type) where
  | zero
  | param (u : ℓ) (n : Name)
  | mvar (u : ℓ) (mvarId : LMVarId)
  deriving Inhabited

def LevelBase.isZero : LevelBase ℓ → Bool
  | .zero => true
  | _ => false

def LevelBase.eq : LevelBase ℓ → LevelBase ℓ → Bool
  | .zero, .zero => true
  | .param _ n, .param _ n' => n == n'
  | .mvar _ mvarId, .mvar _ mvarId' => mvarId == mvarId'
  | _, _ => false

/-- Orders parameters first, metavariables second, zero third. -/
def LevelBase.lt : LevelBase ℓ → LevelBase ℓ → Bool
  | .param _ n, .param _ n' => Lean.Name.lt n n'
  | .param .., .mvar .. => true
  | .param .., .zero .. => true
  | .mvar _ mvarId, .mvar _ mvarId' => (compare mvarId mvarId').isLT
  | .mvar .., .zero .. => true
  | _, _ => false

/--
Used for normalization.
Represents `ipos (base+offset) (ipos ...cond...)`
-/
structure LevelMaxTerm (ℓ : Type) where
  base : LevelBase ℓ
  /-- if `base == .zero` then `offset > 0` -/
  offset : Nat
  /-- parameters and metavariables, in `LevelBase.lt` order. -/
  cond : Array (LevelBase ℓ)
  deriving Inhabited

/--
Compares by base, then `cond` in size, then `cond` in lex order,
then offset in opposite order.
-/
def LevelMaxTerm.lt (t1 t2 : LevelMaxTerm ℓ) : Bool :=
  t1.base.lt t2.base || (t1.base.eq t2.base &&
    t1.cond.size < t2.cond.size || (t1.cond.size == t2.cond.size &&
      have : BEq (LevelBase ℓ) := ⟨LevelBase.eq⟩
      Array.lex t1.cond t2.cond LevelBase.lt || (t1.cond == t2.cond &&
        t1.offset > t2.offset)))

/--
Returns true if `t1 ≥ t2`, hence `t2` is unnecessary (is *subsumed* by `t1`).
-/
def LevelMaxTerm.subsumes (t1 t2 : LevelMaxTerm ℓ) : Bool :=
  (t2.base.isZero || t1.base.eq t2.base)
    && t1.offset ≥ t2.offset
    && t1.cond.all (t2.cond.binSearchContains · LevelBase.lt)

/--
Used for normalization.
Represents `max ...terms...`
-/
structure LevelMaxView (ℓ : Type) where
  /-- Terms in `LevelMaxTerm.lt` order. -/
  terms : Array (LevelMaxTerm ℓ) := #[]
  deriving Inhabited

def LevelMaxView.insert {ℓ} (view : LevelMaxView ℓ) (term : LevelMaxTerm ℓ) :
    LevelMaxView ℓ :=
  { view with terms := view.terms.binInsert LevelMaxTerm.lt term }

/-- Computes the view of `max (u + offset) view`. -/
partial def accLevelMaxView (u : ℓ) (offset : Nat) (view : LevelMaxView ℓ) :
    m (LevelMaxView ℓ) :=
  visit u offset #[] view
where
  visit (u : ℓ) (offset : Nat) (cond : Array (LevelBase ℓ))
      (view : LevelMaxView ℓ) : m (LevelMaxView ℓ) :=
    foldLevelMaxM (init := view) (offset := offset) u fun view u' offset => do
      match (← getLevel u') with
      | .zero =>
        if offset == 0 then
          return view
        else
          return view.insert { base := .zero, offset, cond }
      | .param n =>
        let base := LevelBase.param u' n
        let cond := if offset > 0 then cond else cond.filter (!base.eq ·)
        return view.insert { base, offset, cond }
      | .mvar mvarId =>
        let base := LevelBase.mvar u' mvarId
        let cond := if offset > 0 then cond else cond.filter (!base.eq ·)
        return view.insert { base, offset, cond }
      | .ipos v w =>
        let view := -- `(ipos v w) + offset = max (ipos (v + offset) w) offset`
          if offset == 0 then view
          else view.insert { base := .zero, offset, cond }
        foldIPos w (visit v offset) cond view
      | _ => unreachable!
  foldIPos (w : ℓ)
      (f : Array (LevelBase ℓ) → LevelMaxView ℓ  → m (LevelMaxView ℓ))
      (cond : Array (LevelBase ℓ)) (view : LevelMaxView ℓ) :
      m (LevelMaxView ℓ) :=
    foldLevelMaxM w (init := view) fun view u' offset => do
      if offset > 0 then
        return view
      else
        match (← getLevel u') with
        | .zero => return view
        | .param n =>
          let base := LevelBase.param u' n
          let cond := cond.binInsert LevelBase.lt base
          f cond view
        | .mvar mvarId =>
          let base := LevelBase.mvar u' mvarId
          let cond := cond.binInsert LevelBase.lt base
          f cond view
        | .ipos u v =>
          foldIPos u (foldIPos v f) cond view
        | _ => unreachable!

def mkLevelMaxView (u : ℓ) (offset : Nat := 0) : m (LevelMaxView ℓ) :=
  accLevelMaxView u offset {}

/--
Eliminates terms that are implied by others.
-/
def LevelMaxView.normalize (view : LevelMaxView ℓ) : LevelMaxView ℓ :=
  if view.terms.isEmpty then
    view
  else Id.run do
    let mut currTerm := view.terms[0]!
    let mut baseIdx := 0
    let mut terms := #[currTerm]
    for h : i in [1:view.terms.size] do
      let term := view.terms[i]
      if term.base matches .zero then
        -- Need to compare to *all* previous terms
        if !terms.any (LevelMaxTerm.subsumes · term) then
          terms := terms.push term
      else if term.base.eq currTerm.base then
        -- Can compare to just those with the same base
        if !terms.any (LevelMaxTerm.subsumes · term) (start := baseIdx) then
          terms := terms.push term
      else
        baseIdx := terms.size
        terms := terms.push term
        currTerm := term
    return { terms }

variable [MonadMkLevel m ℓ]

def LevelBase.mkLevel (b : LevelBase ℓ) : m ℓ :=
  match b with
  | .zero => mkLevelZero
  | .param u _ => pure u
  | .mvar u _ => pure u

def LevelMaxTerm.mkLevel (t : LevelMaxTerm ℓ) : m ℓ := do
  let u ← t.base.mkLevel
  let u ← if t.offset > 0 then mkLevelOffset u t.offset else pure u
  if t.cond.isEmpty then
    return u
  else
    let cond ← t.cond.foldrM
      (init := ← t.cond.back!.mkLevel) (start := t.cond.size - 1)
      (fun v acc => do mkLevelIPos (← v.mkLevel) acc)
    mkLevelIPos u cond

def LevelMaxView.mkLevel (view : LevelMaxView ℓ) : m ℓ := do
  let terms := view.terms
  if terms.isEmpty then
    mkLevelZero
  else
    terms.foldrM (init := ← view.terms.back!.mkLevel) (start := terms.size - 1)
      (fun t acc => do mkLevelMax (← t.mkLevel) acc)

/--
Puts a level expression into normal form.
Does not instantiate level metavariables.
-/
def normalizeLevel (u : ℓ) : m ℓ := do
  (← mkLevelMaxView u).normalize.mkLevel

end Normalize

section
variable [MonadMkLevel m ℓ] [MonadGetLevel m ℓ]

/--
Returns true if the levels are equivalent.
-/
partial def levelEquiv [BEq ℓ] (u v : ℓ) : m Bool := do
  if ← levelEq u v then
    return true
  else
    let u ← normalizeLevel u
    let v ← normalizeLevel v
    levelEq u v

/--
Returns true if for all concrete assignments of variables in `u` and `v`
the first is less than or equal to the second.
-/
partial def levelLE (u v : ℓ) : m Bool := do
  let uView ← mkLevelMaxView u
  let vView ← mkLevelMaxView v
  return uView.terms.all (fun t => vView.terms.any (·.subsumes t))

end

end

end LilLean
