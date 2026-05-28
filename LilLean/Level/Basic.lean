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

/--
`mixed` is a hash computation, and `bits` is the lower-order bits encoding
`levelHasParam` and `levelHasMVar`.
-/
private def Level.mkHash (mixed : UInt64) (bits : UInt64) : UInt64 :=
  (mixed &&& ~~~3) ||| (bits &&& 3)

def Level.hashOffset (hv : UInt64) (offset : Nat) : UInt64 :=
  mkHash (mixHash hv offset.toUInt64) hv

/--
Standard hash computation for levels, given a function `getHash` that returns
hashes for levels within `u`.

Lowest two bits encode hasParam (bit 0) and hasMVar (bit 1).
The hash of `Level.zero` is `0`.
-/
def Level.hashCore (u : Level ℓ) (getHash : ℓ → UInt64) : UInt64 :=
  match u with
  | .zero => 0
  | .offset v n =>
    -- Note: we distinguish between `Level.offset (Level.offset u c) d` and
    -- `Level.offset u (c + d)` in the hash computation since they are
    -- structurally different. It is up to `Level` constructions to collapse
    -- offset expressions.
    let hv := getHash v
    hashOffset hv n
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
    mkHash (mixHash 6 hn) 1 -- set bit 0
  | .mvar mvarId =>
    let hm := hash mvarId
    mkHash (mixHash 7 hm) 2 -- set bit 1

/-- Specialization of `Level.hashCore` for hashing a constant level. -/
def Level.hashConst (c : Nat) : UInt64 :=
  if c == 0 then
    0
  else
    hashOffset 0 c

def Level.isZero : Level ℓ → Bool
  | .zero => true
  | _ => false

section
variable {m : Type → Type} [Monad m]

/--
Applies `f` to (non-recursively) update handles.
-/
def Level.mapM (f : ℓ → m ℓ) (u : Level ℓ) : m (Level ℓ) := do
  match u with
  | .zero => return u
  | .offset v n => return .offset (← f v) n
  | .max v w => return .max (← f v) (← f w)
  | .ipos v w => return .ipos (← f v) (← f w)
  | .param _ => return u
  | .mvar _ => return u

section
variable [MonadGetLevel m ℓ]

/--
Returns whether or not the level contains a metavariable.
Note: Even if the metavariables might be assigned with respect to the current
metavariable context, this will still return true.
-/
def levelHasMVar (u : ℓ) : m Bool := do
  return (← levelHash u) &&& 2 > 0

/--
Returns whether or not the level contains a parameter.
-/
def levelHasParam (u : ℓ) : m Bool := do
  return (← levelHash u) &&& 1 > 0

/--
Returns whether or not the level is exactly `Level.zero`.
-/
def isLevelZero (u : ℓ) : m Bool :=
  return (← getLevel u).isZero

/--
Follows `Level.offset` and returns a non-`offset` level plus the total offset.
-/
partial def getLevelOffset (u : ℓ) : m (ℓ × Nat) :=
  go u 0
where
  go (u : ℓ) (c : Nat) : m (ℓ × Nat) := do
    match (← getLevel u) with
    | .offset u' c' => go u' (c + c')
    | _ => return (u, c)

/--
Returns `true` if `u` is equivalent to zero, for all assignments to
metavariables and parameters.
-/
partial def isLevelAlwaysZero (u : ℓ) : m Bool := do
  match (← getLevel u) with
  | .zero => return true
  | .offset v n => pure (n == 0) <&&> isLevelAlwaysZero v
  | .max v w => isLevelAlwaysZero v <&&> isLevelAlwaysZero w
  | .ipos v w => isLevelAlwaysZero v <||> isLevelAlwaysZero w
  | .param _ => return false
  | .mvar _ => return false

/--
Returns `true` if `u` is not equivalent to zero, for all assignments to
metavariables and parameters.
-/
partial def isLevelNeverZero (u : ℓ) : m Bool := do
  match (← getLevel u) with
  | .zero => return false
  | .offset v n => pure (n > 0) <||> isLevelNeverZero v
  | .max v w => isLevelNeverZero v <||> isLevelNeverZero w
  | .ipos v w => isLevelNeverZero v <&&> isLevelNeverZero w
  | .param _ => return false
  | .mvar _ => return false

/--
Returns `true` if `u` and `v` are structurally equal.
-/
partial def levelEq [BEq ℓ] (u v : ℓ) : m Bool := do
  if u == v then
    return true
  if (← levelHash u) != (← levelHash v) then
    return false
  match (← getLevel u), (← getLevel v) with
  | .zero, .zero => return true
  | .offset ua un, .offset va vn => pure (un == vn) <&&> levelEq ua va
  | .max ua ub, .max va vb => levelEq ua va <&&> levelEq ub vb
  | .ipos ua ub, .ipos va vb => levelEq ua va <&&> levelEq ub vb
  | .param un, .param vn => return un == vn
  | .mvar uMVarId, .mvar vMVarId => return uMVarId == vMVarId
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

/-- Makes `u + 1`. -/
def mkLevelSucc (u : ℓ) : m ℓ := do
  mkLevelOffset u 1

section Update
variable [MonadGetLevel m ℓ] [BEq ℓ]

/-- Does `mkLevelOffset newU newC`, but returns `orig` if possible. -/
def updateLevelOffset (orig newU : ℓ) (newC : Nat) : m ℓ := do
  if let .offset u c ← getLevel orig then
    if c == newC && u == newU then
      return orig
  mkLevelOffset newU newC

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

/--
Applies `f` to update handles (non-recursively).
-/
def levelMapM (f : ℓ → m ℓ) (u : ℓ) : m ℓ := do
  match (← getLevel u) with
  | .zero => return u
  | .offset v n => updateLevelOffset u (← f v) n
  | .max v w => updateLevelMax u (← f v) (← f w)
  | .ipos v w => updateLevelIPos u (← f v) (← f w)
  | .param _ => return u
  | .mvar _ => return u

/--
Replaces parameters in `u` using `f`.
-/
partial def levelReplaceParams (f : Name → m (Option ℓ)) (u : ℓ) : m ℓ := do
  if (← levelHasParam u) then
    match (← getLevel u) with
    | .param n =>
      if let some u' ← f n then
        return u'
      else
        return u
    | _ =>
      levelMapM (levelReplaceParams f) u
  else
    return u

/--
Replaces levels in `u` using `f`.
-/
partial def levelReplaceMVars (f : LMVarId → m (Option ℓ)) (u : ℓ) : m ℓ := do
  if (← levelHasMVar u) then
    match (← getLevel u) with
    | .mvar mvarId =>
      if let some u' ← f mvarId then
        return u'
      else
        return u
    | _ =>
      levelMapM (levelReplaceMVars f) u
  else
    return u

end Update

section
variable [MonadGetLevel m ℓ] [BEq ℓ]

/--
Like `mkLevelMax u v`, but returns `u` or `v` if simple checks detect that
one subsumes the other.
-/
partial def mkLevelMax' [BEq ℓ] (u v : ℓ) : m ℓ := do
  let (u', uOffset) ← getLevelOffset u
  let (v', vOffset) ← getLevelOffset v
  if ← levelEq u' v' then
    return if uOffset ≥ vOffset then u else v
  if (← isLevelAlwaysZero u') && uOffset ≤ vOffset then
    return v
  if (← isLevelAlwaysZero v') && uOffset ≥ vOffset then
    return u
  mkLevelMax u v

/--
Like `mkLevelIPos u v`, but returns `0` or `u` if simple checks detect
the expression can be simplified.
-/
partial def mkLevelIPos' [BEq ℓ] (u v : ℓ) : m ℓ := do
  if ← levelEq u v then
    return u
  if (← isLevelAlwaysZero u <||> isLevelAlwaysZero v) then
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
routine if it handles common cases --- in Lean 4, expressions with `imax`
are merely simplified, not normalized --- but in LilLean we opt for a complete
normalization routine.

For levels without any impredicativity handling (i.e., those without `ipos`),
normal forms are straightforward. Given level expressions `u,v,w` and concrete
levels `c,d` ("concrete" means a successor of zero), we have the following
rewrite rules:
- `u + 0 = u`
- `(u + c) + d = u + (c+d)`
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
Knowing whether each variable is zero or positive is sufficient
to simplify and eliminate `ipos` expressions

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

So, we can encode these `f : Set Variable → Level` functions by taking
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
parameter, a metavariable, or an `ipos` expression,
never an `offset` expression.

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

/--
Used for normalization (see `LevelMaxTerm`).
Records the base expression, as well as an existing level expression that
represents it, to reuse it later.
-/
inductive LevelBase (ℓ : Type) where
  | zero
  | param (u : ℓ) (n : Name)
  | mvar (u : ℓ) (mvarId : LMVarId)
  deriving Inhabited

def LevelBase.isZero (b : LevelBase ℓ) : Bool :=
  b matches .zero

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
  /-- if `base.isZero` then `offset > 0` -/
  offset : Nat
  /-- parameters and metavariables (no `.zero`), in `LevelBase.lt` order. -/
  cond : Array (LevelBase ℓ)
  deriving Inhabited

/--
Compares by base, then `cond` in size, then `cond` in lex order,
then offset in descending order.
The purpose of this is for the subsumption check: we only need to check
subsumption (with `LevelMaxTerm.subsumes`) if `t1.lt t2`.
-/
def LevelMaxTerm.lt (t1 t2 : LevelMaxTerm ℓ) : Bool :=
  have : BEq (LevelBase ℓ) := ⟨LevelBase.eq⟩
  t1.base.lt t2.base || (t1.base == t2.base &&
    t1.cond.size < t2.cond.size || (t1.cond.size == t2.cond.size &&
      Array.lex t1.cond t2.cond LevelBase.lt || (t1.cond == t2.cond &&
        t1.offset > t2.offset)))

/--
Returns true if `t1 ≥ t2` as level expressions,
hence `t2` is unnecessary (is *subsumed* by `t1`).
-/
def LevelMaxTerm.subsumes (t1 t2 : LevelMaxTerm ℓ) : Bool :=
  t1.offset ≥ t2.offset
    && (t2.base.isZero || t1.base.eq t2.base)
    && t1.cond.all (t2.cond.binSearchContains · LevelBase.lt)

def LevelMaxTerm.eq (t1 t2 : LevelMaxTerm ℓ) : Bool :=
  have : BEq (LevelBase ℓ) := ⟨LevelBase.eq⟩
  t1.offset == t2.offset && t1.base == t2.base && t1.cond == t2.cond

/--
Used for normalization. Represents `max ...terms...`
-/
structure LevelMaxView (ℓ : Type) where
  /-- Terms in `LevelMaxTerm.lt` order. -/
  terms : Array (LevelMaxTerm ℓ) := #[]
  deriving Inhabited

def LevelMaxView.insert {ℓ} (view : LevelMaxView ℓ) (term : LevelMaxTerm ℓ) :
    LevelMaxView ℓ :=
  { view with terms := view.terms.binInsert LevelMaxTerm.lt term }

def LevelMaxView.eq (view1 view2 : LevelMaxView ℓ) : Bool :=
  have : BEq (LevelMaxTerm ℓ) := ⟨LevelMaxTerm.eq⟩
  view1.terms == view2.terms

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
def LevelMaxView.simplify (view : LevelMaxView ℓ) : LevelMaxView ℓ :=
  if view.terms.isEmpty then
    view
  else Id.run do
    let mut currTerm := view.terms[0]!
    let mut baseIdx := 0
    let mut terms := #[currTerm]
    for h : i in [1:view.terms.size] do
      let term := view.terms[i]
      if term.base matches .zero then
        -- Need to check subsumption with *all* previous terms
        if !terms.any (LevelMaxTerm.subsumes · term) then
          terms := terms.push term
      else if term.base.eq currTerm.base then
        -- Can check subsumption with just those with the same base
        if !terms.any (LevelMaxTerm.subsumes · term) (start := baseIdx) then
          terms := terms.push term
      else
        baseIdx := terms.size
        terms := terms.push term
        currTerm := term
    return { terms }

/--
Returns true if the level is already obviously in normal form.
This is used to save work while normalizating level expressions.
This currently handles everything that doesn't have `ipos` expressions.
-/
partial def levelIsAlreadyNormalizedQuick (u : ℓ) : m Bool := do
  if (← getAtom? u).isSome then
    return true
  else
    match (← getLevel u) with
    | .max v w =>
      let some (b, c) ← getAtom? v | return false
      visitMax b c w
    | _ => return false
where
  getAtom? (u : ℓ) : m (Option (LevelBase ℓ × Nat)) := do
    let (u, u', c) ←
      match (← getLevel u) with
      | .offset v c =>
        if c == 0 then return none
        else pure (v, ← getLevel v, c)
      | u' => pure (u, u', 0)
    match u' with
    | .zero => return some (.zero, c)
    | .param n => return some (.param u n, c)
    | .mvar mvarId => return some (.mvar u mvarId, c)
    | _ => return none
  visitMax (curr : LevelBase ℓ) (maxOffset : Nat) (u : ℓ) : m Bool := do
    match (← getLevel u) with
    | .max v w =>
      let some (b, c) ← getAtom? v | return false
      unless curr.lt b do return false
      visitMax b (max maxOffset c) w
    | _ =>
      let some (b, c) ← getAtom? u | return false
      unless curr.lt b do return false
      if b.isZero then
        return maxOffset < c
      else
        return true

variable [MonadMkLevel m ℓ]

def LevelBase.mkLevel (b : LevelBase ℓ) : m ℓ :=
  match b with
  | .zero => mkLevelZero
  | .param u _ => pure u
  | .mvar u _ => pure u

def LevelMaxTerm.mkLevel (t : LevelMaxTerm ℓ) : m ℓ := do
  let u ← t.base.mkLevel
  let u ← mkLevelOffset u t.offset
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

Uses an evaluation/simplification/reflection approach, using `LevelMaxView`
as an intermediate representation.
-/
def normalizeLevel (u : ℓ) : m ℓ := do
  if ← levelIsAlreadyNormalizedQuick u then
    return u
  else
    (← mkLevelMaxView u).simplify.mkLevel

end Normalize

section
variable [MonadMkLevel m ℓ] [MonadGetLevel m ℓ]

/--
Returns true if the levels are equivalent.
We do this by checking that the normalized levels are equal,
that is, the reference implementation is
```
levelEq (← normalizeLevel u) (← normalizeLevel v)
```
However, we can skip the reification step and compare `LevelMaxView`s directly.
-/
partial def levelEquiv [BEq ℓ] (u v : ℓ) : m Bool := do
  if ← levelEq u v then
    return true
  else
    let uView := (← mkLevelMaxView u).simplify
    let vView := (← mkLevelMaxView v).simplify
    return uView.eq vView

/--
Returns true if for all concrete assignments of variables in `u` and `v`
the first is less than or equal to the second.

If `levelLE u v` and `levelLE v u` then `levelEquiv u v`.
-/
partial def levelLE (u v : ℓ) : m Bool := do
  let uView ← mkLevelMaxView u
  let vView ← mkLevelMaxView v
  return uView.terms.all (fun t => vView.terms.any (·.subsumes t))

end

end

end LilLean
