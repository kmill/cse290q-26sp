import Batteries

/-!
# Elimination and recursion (continued)

Today, two somewhat unrelated topics:
  1. How does the metavariable context work?
     And how does it support tactic elaboration?
  2. How does structural recursion work?

We'll also touch upon the implementation of *dependent elimination*
(a.k.a. dependent pattern matching).

-/

/-!
## Metavariable contexts

Recall that a *metavariable* consists of the following things, managed by
the metavariable context:

- A unique identifier (an "`MVarId`") to refer to a metavariable by.
  (These are embedded within expressions using `Expr.mvar` nodes.)

- An associated local context.

- A type that is valid with respect to this local context.

- Possibly, an assignment, which is an expression valid with respect to this
  local context, and whose type is defeq to the metavariable's type.

For example, if `?m` is a metavariable with context
```
α : Type
f : α → α
```
and with type `α → α`, then it is valid to assign `?m := fun x : α => f (f x)`.

no:
?m := α  (α : Type, but it needs to have type `α → α`)
?m := z  (where z is some free variable not in context)
-/

/-!
### Metavariable instantiation

Given an expression `e`, *instantiating* the metavariables in `e` means to
substitute any assignments for those metavariables.

In Lean, `instantiateMVars : Expr → MetaM Expr` does instantiation.
-/


/-!
### Other components of metavariables

There is additional data associated to metavariables:

- The *user name* is a name that can be used to refer to the metavariable.
  Writing `?foo` looks up the metavariable named `foo`, or else creates one
  with that name.

- The *index* records the order in which metavariables were created, enabling
  tactics like `refine` to determine which metavariables are new and should
  become new goals.

- The *kind* determines whether the metavariable can be solved for by
  unification and which abstraction procedure to use.

  - *natural* metavariables are solvable by unification.

  - *synthetic (instance)* metavariables are like natural metavariables, but
    solved for by typeclass inference. Unification avoids solving for them if
    it can solve for other metavariables instead. It can also trigger typeclass
    inference in an attempt to unstick unification.

  - *synthetic opaque* metavariables are opaque constants that are
    solved for by user code (e.g. `by ...` and other elaboration processes).
    They are usually not solvable by unification, unless a metaprogram
    specifically allows assignment to them.

-/



/-!
### Abstraction of free variables

Key problem: transporting expressions to different scopes.

  If a metavariable appears inside a binding construct

     fun x : X => ?m

  while we're inside `fun x => ...`, the local context contains `x : X`,
  and the metavariable `?m` naturally should be able to refer to `x`.

  However, `x` must somehow be translated into the De Bruijn
  variable `Expr.bvar 0`.
  (If `?m := f x`, it would be incorrect to substitute `f x` directly into
  this expression.)

  Who is responsible for the translation, and how?

The `mkLambdaFVars #[fvars...] e` and `mkForallFVars #[fvars...] e` functions
are responsible for taking an expression `e` that may contain metavariables
and then creating a new lambda/pi expression that correctly abstracts the
given free variables from `e`, possibly **modifying** the metavariables in `e`
in the process.

Insight: a metavariable `?m` is sort of like a function, whose parameters are
the variables in the local context. We can always *revert* variables, creating
a new metavariable `?m'` whose type is a pi type (an actual function) and
whose local context does not include these variables, and then
assign `?m := ?m' x y z`.

-/

/-!
#### Solution 1 (used for natural and synthetic metavariables)

Given `?m : M`, to construct `fun x : T => ?m`, we revert `x` and create
the metavariable `?m' : (x : T) → M` with `x` removed from its local context.
Then we assign
  `?m := ?m' x`
Since `?m'` does not depend on `x`, we can safely replace `x` with a De Bruijn
variable. Then `fun x : T => ?m` is
  `fun x : T => ?m' #0`  (where `#0` is the De Bruijn variable `.bvar 0`)

Note: `M` may depend on `x`. It may contain metavariables, so we may need
to recursively apply this abstraction procedure!
-/
variable (T M : Type) in
#check fun x : T => (_ : M)

/-!
This has a notable downside.
*The abstraction procedure does not preserve the original local context.*
This means such metavariables are unsuitable for representing tactic goal
states.

For example, consider
-/
example (p q : Prop) : p → q := by
  intro h
  sorry
example (p q : Prop) : p → q :=
  fun h => by
    sorry
/-!
The `intro h` tactic is equivalent to `refine fun h : p => ?_`.
The new goal `?_` should have `h : p` in its local context.
However, if we do "solution 1", we assign to `?_` a new metavariable
whose type is `p → q` (to revert `h`).

That defeats the whole purpose of `intro`!
-/

/-!
#### Solution 2 (used by synthetic opaque metavariables)

Recall that in the above we made the assignment `?m := ?m' x`.
Assigning `?m` leads to loss of original local context.
We can do two things:

- First, let's make `?m` be an opaque constant that's not assignable except
  by its "owner".

- Second, let's instead treat this as a defeq constraint `?m ≟ ?m' x`
  that we postpone until we can make progress.
  We will ensure the constraint is uniquely solvable, so it's not a matter
  of "if" but "when".

Since `?m'` does not have `x` in its local context, this is a "Miller pattern",
and so it is uniquely solvable, once `?m` is a fully instantiated expression.
If `?m := e`, then we will be able to assign `?m' := fun x' => e[x:=x']`.
More accurately, we do `?m' x' := e[x:=x']` for all `x'`.

Lean calls this a *delayed assignment*.

Back to the `intro` example,
-/
example (p q : Prop) : p → q := by
  intro h
  sorry
/-!
This starts with the goal `?g : p → q`.
It constructs `fun h : p => (?g' : q)`, where `?g'` is synthetic opaque.
During abstraction, it creates `?g'' : p → q`
and then postpones `?g' ≟ ?g'' h`.
Finally it assigns `?g := fun h : p => ?g'' h`
and sets the new goal to be `?g'`.

The metavariable `?g'` has a local context with `h : p`, which is what we
want of the new goal.
-/
open Lean Meta Elab Tactic in
elab "my_intro " h:ident : tactic => do
  let g ← getMainGoal
  g.withContext do
    let gTy ← whnf (← g.getType)
    let .forallE _ hTy gTyBody bi := gTy
      | throwError "goal is not a pi type"
    withLocalDecl h.getId bi hTy fun x => do
      let gTyBody := gTyBody.instantiate1 x
      let g' ← mkFreshExprSyntheticOpaqueMVar gTyBody
      let pf ← mkLambdaFVars #[x] g'
      g.assign pf
      replaceMainGoal [g'.mvarId!]

example (p q : Prop) : p → q := by
  show_term my_intro h
  sorry

/-!
## Basic tactics

- `refine e`
  elaborates `e` to solve the main goal
  and new metavariables in `e` become new goals

- `exact e`
  like `refine e` but throws an error instead of creating new goals
  (`refine e <;> done`)

- `apply e`
  like `refine e ?_ ... ?_`, figuring out how many `?_`'s to insert

- `intro h`
  does `refine fun h => ?_`

- `constructor`
  figures out which inductive type `I` the goal is for, then takes the
  first constructor `I.ctor` such that
  `refine I.ctor ?_ ... ?_` works

- `rw [thm]`
  elaborates `thm _ ... _ : lhs = rhs`
  takes the goal `g : T`, figures out a `motive` function such that
  `T ≟ motive lhs`
  then uses `Eq.rec` to change the goal to `motive rhs`

- `let x : T := v`
  does `refine let x : T := v; ?_`
  (similarly for `have`)

- `cases x` in its basic form does the following:
  takes the recursor `I.recOn`/`I.casesOn` for `x : I ...`,
  figures out a `motive` function such that for the goal `g : T`,
  `T ≟ motive x`
  then uses `I.casesOn x (motive := motive) ?minor1 ?minor2 ...`
  to solve the goal creating new goals for the minor premises.
  The `induction` tactic is similar, but uses `I.recOn`.
  (Also: if there are hypotheses that depend on `x`, then are automatically
  reverted then introduced ("generalized"), and if `I` has indices, there
  is some *dependent elimination* technique.)

-/

/-!
## Non-dependent elimination

First, let's look at how `induction` works in the non-dependent case.
-/

def tri (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => tri n' + (n' + 1)

example (n : Nat) : n ≤ tri n := by
  induction n
  · unfold tri
    apply Nat.le_refl
  · rename_i n ih
    unfold tri
    refine Nat.add_le_add ih ?_
    apply Nat.le_add_left

-- Manually:
example (n : Nat) : n ≤ tri n := by
  refine Nat.recOn (motive := fun n => n ≤ tri n)
    n ?zero ?succ
  all_goals dsimp only [Nat.succ_eq_add_one]
  · unfold tri
    apply Nat.le_refl
  · clear n
    intro n ih
    unfold tri
    refine Nat.add_le_add ih ?_
    apply Nat.le_add_left

/-!
## Dependent elimination

First, let's look at how `induction` works in the non-dependent case.
-/

/-!
Dependent elimination refers to applying elimination principles
where the patterns have dependencies.
-/

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n} (head : α) (tail : Vec α n) : Vec α (n + 1)

inductive Vec.all {α : Type u} (P : α → Prop) :
    {n : Nat} → (v : Vec α n) → Prop
  | nil :
    Vec.all P Vec.nil
  | cons {n : Nat} {head : α} {tail : Vec α n} :
    P head → Vec.all P tail → Vec.all P (Vec.cons head tail)

theorem vec_ex1 {α : Type u} (P : α → Prop) :
  {n : Nat} → (v : Vec α (n+1)) → Vec.all P v → ∃ (x : α), P x
| _, Vec.cons head _, Vec.all.cons h _ => ⟨head, h⟩

theorem vec_ex2 {α : Type u} (P : α → Prop) :
  {n : Nat} → (v : Vec α (n+1)) → Vec.all P v → ∃ (x : α), P x
| .(n), @Vec.cons _ n head _, Vec.all.cons h _ => ⟨head, h⟩

theorem vec_ex3 {α : Type u} (P : α → Prop)
    {n : Nat} (v : Vec α (n+1)) (hv : Vec.all P v) : ∃ (x : α), P x := by?
  cases hv
  rename_i head h _ _
  exact ⟨head, h⟩

#check Vec.all.casesOn

theorem vec_ex4 {α : Type u} (P : α → Prop)
    {n : Nat} (v : Vec α (n+1)) (ha : Vec.all P v) : ∃ (x : α), P x := by
  generalize hn : n+1 = n' at v
  generalize hv : v = v' at ha
  revert v hn n
  refine Vec.all.casesOn (n := n') (v := v') ha ?_ ?_
  · intro h
    exact Nat.noConfusion h
  · intro _ head _ h _ _ _ _
    exact ⟨head, h⟩


---
