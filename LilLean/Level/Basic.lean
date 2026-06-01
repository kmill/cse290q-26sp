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

protected def Level.eq [BEq ℓ] (u v : Level ℓ) : Bool :=
  match u, v with
  | .zero, .zero => true
  | .offset ua un, .offset va vn => un == vn && ua == va
  | .max ua ub, .max va vb => ua == va && ub == vb
  | .ipos ua ub, .ipos va vb => ua == va && ub == vb
  | .param un, .param vn => un == vn
  | .mvar uMVarId, .mvar vMVarId => uMVarId == vMVarId
  | _, _ => false

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

/-- Specialization of `Level.hashCore` to hashing a constant level. -/
def Level.hashConst (c : Nat) : UInt64 :=
  if c == 0 then
    0
  else
    hashOffset 0 c

instance [Hashable ℓ] : Hashable (Level ℓ) where
  hash u := Level.hashCore u hash

def Level.isZero : Level ℓ → Bool
  | .zero => true
  | _ => false

/--
Applies `f` to (non-recursively) modify handles.
-/
def Level.map {ℓ ℓ'} (f : ℓ → ℓ') (u : Level ℓ) : Level ℓ' :=
  match u with
  | .zero => .zero
  | .offset v n => .offset (f v) n
  | .max v w => .max (f v) (f w)
  | .ipos v w => .ipos (f v) (f w)
  | .param n => .param n
  | .mvar mvarId => .mvar mvarId

instance : Functor Level where
  map := Level.map

def LevelGetter.mkLevel' (ctx : LevelGetter ℓ) (u : ℓ) : Level' ctx :=
  { handle := u }

namespace Level'
variable {ctx : LevelGetter ℓ}

def get (u : Level' ctx) : Level (Level' ctx) :=
  ctx.mkLevel' <$> (ctx.getLevel u.handle)

def hash (u : Level' ctx) : UInt64 := ctx.levelHash u.handle

/--
Returns true if the level contains a parameter.
-/
def hasParam (u : Level' ctx) : Bool := u.hash &&& 1 > 0

/--
Returns true if the level contains a metavariable.
(Note: true even if the metavariable is assigned.)
-/
def hasMVar (u : Level' ctx) : Bool := u.hash &&& 2 > 0

/--
Returns true if the level is exactly `Level.zero`.
-/
def isZero (u : Level' ctx) : Bool := u.get.isZero

/--
Follows `Level.offset` and returns a non-`offset` level plus the total offset.
-/
partial def getOffset (u : Level' ctx) : Level' ctx × Nat :=
  go u 0
where
  go (u : Level' ctx) (c : Nat) : Level' ctx × Nat :=
    match u.get with
    | .offset u' c' => go u' (c + c')
    | _ => (u, c)

/--
Returns `true` if `u` is equivalent to zero, for all assignments to
metavariables and parameters.
-/
partial def isAlwaysZero (u : Level' ctx) : Bool :=
  match u.get with
  | .zero => true
  | .offset v n => n == 0 && isAlwaysZero v
  | .max v w => isAlwaysZero v && isAlwaysZero w
  | .ipos v w => isAlwaysZero v || isAlwaysZero w
  | .param _ => false
  | .mvar _ => false

/--
Returns `true` if `u` is not equivalent to zero, for all assignments to
metavariables and parameters.
-/
partial def isNeverZero (u : Level' ctx) : Bool :=
  match u.get with
  | .zero => false
  | .offset v n => n > 0 || isNeverZero v
  | .max v w => isNeverZero v || isNeverZero w
  | .ipos v w => isNeverZero v && isNeverZero w
  | .param _ => false
  | .mvar _ => false

/--
Returns `true` if `u` and `v` are structurally equal.
This implements the `BEq` instance for `Level'`.
-/
protected partial def eq [BEq ℓ] (u v : Level' ctx) : Bool :=
  let : BEq (Level (Level' ctx)) :=
    let : BEq (Level' ctx) := ⟨Level'.eq⟩
    ⟨Level.eq⟩
  if u.handle == v.handle then
    true
  else if u.hash != v.hash then
    false
  else
    u.get == v.get

instance [BEq ℓ] : BEq (Level' ctx) where
  beq := Level'.eq

end Level'

section
variable {m : Type → Type} [Monad m]

/--
Applies `f` to (non-recursively) modify handles.
-/
def Level.mapM {ℓ ℓ'} (f : ℓ → m ℓ') (u : Level ℓ) : m (Level ℓ') := do
  match u with
  | .zero => return .zero
  | .offset v n => return .offset (← f v) n
  | .max v w => return .max (← f v) (← f w)
  | .ipos v w => return .ipos (← f v) (← f w)
  | .param n => return .param n
  | .mvar mvarId => return .mvar mvarId

section
variable [MonadGetLevel m ℓ]

/-- See `Level'.hasParam` -/
def levelHasParam (u : ℓ) : m Bool := do
  return (← getLevelGetter).mkLevel' u |>.hasParam

/-- See `Level'.hasMVar` -/
def levelHasMVar (u : ℓ) : m Bool := do
  return (← getLevelGetter).mkLevel' u |>.hasMVar

/-- See `Level'.isZero` -/
def isLevelZero (u : ℓ) : m Bool :=
  return (← getLevelGetter).mkLevel' u |>.isZero

/-- See `Level'.getOffset` -/
partial def getLevelOffset (u : ℓ) : m (ℓ × Nat) := do
  let (u', c) := (← getLevelGetter).mkLevel' u |>.getOffset
  return (u'.handle, c)

/-- See `Level'.isAlwaysZero` -/
partial def isLevelAlwaysZero (u : ℓ) : m Bool :=
  return (← getLevelGetter).mkLevel' u |>.isAlwaysZero

/-- See `Level'.isNeverZero` -/
partial def isLevelNeverZero (u : ℓ) : m Bool := do
  return (← getLevelGetter).mkLevel' u |>.isNeverZero

/--
Returns `true` if `u` and `v` are structurally equal.
See `Level'.levelEq`.
-/
partial def levelEq [BEq ℓ] (u v : ℓ) : m Bool := do
  let ctx ← getLevelGetter
  return ctx.mkLevel' u == ctx.mkLevel' v

end

section
variable [MonadMkLevel m ℓ]

/-- Makes `Level.zero`. -/
def mkLevelZero : m ℓ := mkLevel .zero

/-- `mkLevelOffset u n` makes `Level.offset u n`. Returns `u` if `n = 0`. -/
def mkLevelOffset (u : ℓ) (n : Nat) : m ℓ := mkLevel (.offset u n)

/-- Makes `Level.max u v`. -/
def mkLevelMax (u v : ℓ) : m ℓ := mkLevel (.max u v)

/-- Makes `Level.ipos u v`. This represents `if v > 0 then u else 0`. -/
def mkLevelIPos (u v : ℓ) : m ℓ := mkLevel (.ipos u v)

/-- Makes `Level.param n`. -/
def mkLevelParam (n : Name) : m ℓ := mkLevel (.param n)

/-- Makes `Level.mvar mvarId`. -/
def mkLevelMVar (mvarId : LMVarId) : m ℓ := mkLevel (.mvar mvarId)

/-- Makes `Level.zero + n`. -/
def mkLevelConst (n : Nat) : m ℓ := do
  mkLevelOffset (← mkLevelZero) n

/-- Makes `imax u v`, which is zero if `v = 0` and otherwise `max u v`. -/
def mkLevelIMax (u v : ℓ) : m ℓ := do
  mkLevelMax (← mkLevelIPos u v) v

/-- Makes `u + 1`. -/
def mkLevelSucc (u : ℓ) : m ℓ := do
  mkLevelOffset u 1

def mkLevelMaxN (us : Array ℓ) : m ℓ := do
  if h : us.size = 0 then
    mkLevelZero
  else
    us.foldrM (start := us.size - 1) (init := us.back) mkLevelMax

section Update
variable [MonadGetLevel m ℓ] [BEq ℓ]

/-- Does `mkLevelOffset newU newC`, but returns `orig` if possible. -/
def updateLevelOffset (orig newU : ℓ) (newC : Nat) : m ℓ := do
  if let .offset u c ← getLevel orig then
    if c == newC && u == newU then
      return orig
  mkLevelOffset newU newC

/-- Does `mkLevelMax newU newV`, but returns `orig` if possible. -/
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
Like `Level.mapM` but attempts to reuse the original level.
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
Replaces level metavariables in `u` using `f`.
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

def mkLevelMaxN' (us : Array ℓ) : m ℓ := do
  if h : us.size = 0 then
    mkLevelZero
  else
    us.foldrM (start := us.size - 1) (init := us.back) mkLevelMax'

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

/--
Folds over all components of a `max` level expression while distributing
offsets. Calls `f` with each `u'+offset` pair. The level `u'` is zero, a
parameter, a metavariable, or an `ipos` expression,
never an `offset` expression.

For example, `max ((max u v) + 2) w` will call `f` on `u+2`, `v+2`, and `f w`.
-/
partial def LevelGetter.foldLevelMaxM (ctx : LevelGetter ℓ) {α : Type}
    (u : ℓ) (f : α → ℓ → Nat → α) (init : α) (offset : Nat := 0) :
    α :=
  go (ctx.mkLevel' u) offset init
where
  go (u : Level' ctx) (offset : Nat) (init : α) : α :=
    let (u', uOffset) := u.getOffset
    let offset' := offset + uOffset
    match u'.get with
    | .max v w => go w offset' (go v offset' init)
    | _ => f init u'.handle offset'

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
partial def LevelGetter.accLevelMaxView (ctx : LevelGetter ℓ)
    (u : ℓ) (offset : Nat) (view : LevelMaxView ℓ) :
    LevelMaxView ℓ :=
  visit u offset #[] view
where
  visit (u : ℓ) (offset : Nat) (cond : Array (LevelBase ℓ))
      (view : LevelMaxView ℓ) : LevelMaxView ℓ :=
    ctx.foldLevelMaxM (init := view) (offset := offset) u fun view u' offset =>
      match ctx.getLevel u' with
      | .zero =>
        if offset == 0 then
          view
        else
          view.insert { base := .zero, offset, cond }
      | .param n =>
        let base := LevelBase.param u' n
        let cond := if offset > 0 then cond else cond.filter (!base.eq ·)
        view.insert { base, offset, cond }
      | .mvar mvarId =>
        let base := LevelBase.mvar u' mvarId
        let cond := if offset > 0 then cond else cond.filter (!base.eq ·)
        view.insert { base, offset, cond }
      | .ipos v w =>
        let view := -- `(ipos v w) + offset = max (ipos (v + offset) w) offset`
          if offset == 0 then view
          else view.insert { base := .zero, offset, cond }
        foldIPos w (visit v offset) cond view
      | _ => unreachable!
  foldIPos (w : ℓ)
      (f : Array (LevelBase ℓ) → LevelMaxView ℓ  → LevelMaxView ℓ)
      (cond : Array (LevelBase ℓ)) (view : LevelMaxView ℓ) :
      LevelMaxView ℓ :=
    ctx.foldLevelMaxM w (init := view) fun view u' offset =>
      if offset > 0 then
        view
      else
        match ctx.getLevel u' with
        | .zero => view
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

def LevelGetter.mkLevelMaxView (ctx : LevelGetter ℓ)
    (u : ℓ) (offset : Nat := 0) : LevelMaxView ℓ :=
  ctx.accLevelMaxView u offset {}

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
partial def LevelGetter.levelIsAlreadyNormalizedQuick
    (ctx : LevelGetter ℓ) (u : ℓ) : Bool :=
  (getAtom? u).isSome ||
    match ctx.getLevel u with
    | .max v w =>
      if let some (b, c) := getAtom? v then
        visitMax b c w
      else
        false
    | _ => false
where
  getAtom? (u : ℓ) : Option (LevelBase ℓ × Nat) := do
    let (u, u', c) ←
      match ctx.getLevel u with
      | .offset v c =>
        if c == 0 then none
        else some (v, ctx.getLevel v, c)
      | u' => some (u, u', 0)
    match u' with
    | .zero => some (.zero, c)
    | .param n => some (.param u n, c)
    | .mvar mvarId => some (.mvar u mvarId, c)
    | _ => none
  visitMax (curr : LevelBase ℓ) (maxOffset : Nat) (u : ℓ) : Bool :=
    match ctx.getLevel u with
    | .max v w =>
      if let some (b, c) := getAtom? v then
        curr.lt b && visitMax b (max maxOffset c) w
      else
        false
    | _ =>
      if let some (b, c) := getAtom? u then
        curr.lt b && (!b.isZero || maxOffset < c)
      else
        false

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
def normalizeLevel [MonadGetLevel m ℓ] (u : ℓ) : m ℓ := do
  let ctx ← getLevelGetter
  if ctx.levelIsAlreadyNormalizedQuick u then
    return u
  else
    (ctx.mkLevelMaxView u).simplify.mkLevel

end Normalize

def Level'.mkLevelMaxView {ctx : LevelGetter ℓ} (u : Level' ctx) :
    LevelMaxView ℓ :=
  ctx.mkLevelMaxView u.handle

def Level'.equiv {ctx : LevelGetter ℓ} [BEq ℓ] (u v : Level' ctx) : Bool :=
  u == v || u.mkLevelMaxView.eq v.mkLevelMaxView

def Level'.le {ctx : LevelGetter ℓ} [BEq ℓ] (u v : Level' ctx) : Bool :=
  u == v ||
    let uView := u.mkLevelMaxView
    let vView := v.mkLevelMaxView
    uView.terms.all (fun t => vView.terms.any (·.subsumes t))

/--
Returns true if the levels are equivalent.
We do this by checking that the normalized levels are equal,
that is, the reference implementation is
```
levelEq (← normalizeLevel u) (← normalizeLevel v)
```
However, we can skip the reification step and compare `LevelMaxView`s directly.
-/
def levelEquiv [MonadGetLevel m ℓ] [BEq ℓ] (u v : ℓ) : m Bool := do
  let ctx ← getLevelGetter
  return Level'.equiv (ctx.mkLevel' u) (ctx.mkLevel' v)

/--
Returns true if for all concrete assignments of variables in `u` and `v`
the first is less than or equal to the second.

If `levelLE u v` and `levelLE v u` then `levelEquiv u v`.
-/
partial def levelLE [MonadGetLevel m ℓ] [BEq ℓ] (u v : ℓ) : m Bool := do
  let ctx ← getLevelGetter
  return Level'.le (ctx.mkLevel' u) (ctx.mkLevel' v)

end

end LilLean
