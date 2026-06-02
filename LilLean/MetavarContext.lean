/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.LocalContext

/-!
# Metavariable context

This module defines the metavariable context, which manages level and expression
metavariables. The metavariable context is also responsible for abstracting free
variables from expressions that contain metavariables with contexts depending on
those variables. These are foundational algorithms for term elaboration.
It is also somewhat subtle and technical, hence this long module docstring.

Something we do in LilLean is have the metavariable context interface with
the region-based memory allocation in the `LevelContext` and `ExprContext`.
The metavariable context manages back-pointers from older to newer regions
via metavariable assignments, and metavariable instantiation is used to trace
expressions as a garbage collection process before regions are deallocated.

## The problem of scope linkage

In the simplest case, of expressions in an empty local context, metavariables
are easy: they represent "holes" in an expression. After assigning expressions
to the metavariables, they can be *instantiated* by simple substitution.

However, local contexts are generally not empty. A metavariable with respect
to a given local context can have an assignment that contains free variables
from that context. Suppose we are elaborating `fun x : T => ?m`. The local
context `?m` has an additional `x : T` that is not in scope outside the `fun`.
Recall that `Expr` uses De Bruijn indices to encode bindings. We somehow need
to link together two scoping concepts:

- expressions assigned to `?m` may contain the free variable `x`, since that's
  what's in the local context at `?m`;

- but at the same time, the correct expression to use would be `Expr.bvar 0`,
  since the correct encoding is a De Bruijn variable, not a free variable.

This requires mechanisms to convert between these.

The basic solution is we can create an auxiliary metavariable `?m'` with a
pi type and with a local context not containing `x`, and then we can
assign `?m := ?m' x`. With this assignment, we can abstract `x` from `?m` and
construct the function expression `fun x => ?m' x`, where the applied `x` is a
De Bruijn variable The key facts are (1) by *reverting* `x` to create `?m'`, we
get a new metavariable that no longer has `x` in scope and (2) the metavariable
can still, indirectly, depend on `x` since one can still assign a function to
`?m'` that makes use of this `.bvar 0` argument (note: this suggests that when
instantiating metavariable assignments, we ought to reduce any beta redexes
thus created).

Put another way, while `exprAbstractFVarRev` is able to abstract free variables
that are actually present in an expression, it is not able to take into account
metavariable dependencies on free variables. We can create new metavariables
that "revert" these dependencies. Since this eliminates dependencies, it enables
`exprAbstractFVarRev` to correctly abstract free variables.

Observe: a "metavariable" comprises an entire application `?m' x₁ x₂ ... xₙ`.
The expressions applied to `?m` are often bvars or fvars, but they can be any
expression, and they represent the way in which variables from the local context
for `?m` are linked to the surrounding scope.

Note that in this basic scheme the lifetime of a metavariable effectively ends
once a free variable it depends on is abstracted (and the metavariable appears
in an expression being abstracted as such). The exact local context does not
survive.

For many uses of metavariables, this is OK. A metaprogram will enter the
telescope of a metavariable's type as needed, construct an expression, abstract,
assign, and repeat. One can imagine that every metaprogram begins with `intros`.

We wish to go beyond this basic solution and preserve the ability to assign
`?m` itself, with its original local context and `FVarId`s.

### Elaboration complications

The basic solution causes complications for metavariables representing postponed
elaboration problems (e.g. tactics). For example, consider a goal `?g₁ : p → q`.
The `intro h` tactic operates by assigning `?g₁ := fun h : p => ?g₂`. If we
follow the reversion process described above, we would create `?g₂' : p → q`
and assign `?g₂ := ?g₂' h` to eliminate the dependence on `h : p`. However,
this completely defeats the purpose, since the new goal `?g₂'` has the exact
same type as what we started with!

We need a mechanism to preserve the local context at `?g₂`. The lifetime
of the local context needs to persist beyond the scope of `fun`.

In Lean 4, the concept of *delayed assignment* solves this problem. In a
delayed assignment, we create the metavariable `?g₂'` in essentially the same
way, but we make the assignment "in reverse", as `?g₂' h := ?g₂`. The actual
assignment is delayed until `?g₂` is *fully assigned* (meaning `?g₂` contains no
metavariables once instantiated), and then, since this is a *Miller pattern*,
this higher-order unification has a unique solution `?g₂' x := ?g₁[h := x]`. By
delaying until `?g₁` is fully assigned, `exprAbstractFVarRev` can correctly
abstract `h`. (Note that `?g₂'` doesn't get assigned to the lambda expression
`?g₂' := fun x => g₁[h := x]`. When there are `let` definitions, such an
expression might not even be type correct.)

Delayed assignment has some drawbacks. For one, the assignment does not occur
until the metavariable is fully assigned, which is a strong condition that can
lead to unnecessary elaboration failures. For another, the delayed assigned
metavariable `?g₂'` is effectively unassignable. Normally we want to avoid
unification, since it was found to lead to counterintuitive behavior if
unification could assign tactic metavariables during elaboration itself, but as
part of the normal operation of a tactic such unification can be desired.
The `refine` tactic for example does unification post-elaboration while ensuring
the type is definitionally equal to the goal.

LilLean takes a different approach from Lean 4, decoupling opacity from
abstraction behavior. The `MetavariableKind` records assignability of
metavariables, and we *always* do delayed assignments. We avoid the drawbacks
from delayed assignments through two strategies:

1. We don't allow abstracting a metavariable with respect to multiple sets
   of free variables --- instead, we have a single associated abstraction, and
   whenever further abstraction is needed we add free variables to the set,
   create a new "`?m'`", and assign the old "`?m'`". We also act as if `?m`
   has been assigned to `?m' x₁ ... xₙ` during instantiation, even though it is
   not yet assigned.

2. We allow instantiation of partially assigned delayed assignments. This
   involves abstracting the abstracted free variables from the metavariables
   in the expression. This process is benefitted by 1.

Instantiating partially assigned delayed assignments does not always need doing.
We may consider not instantiating opaque metavariables eagerly, but only when
forced (TBD).

This is "lazy" abstraction. We can imagine instead always abstracting `?g₂`
fully, creating a metavariable `?g₂'` with an empty local context.
Such a metavariable never requires further abstraction. This would be at a loss
of efficiency however, from all the overhead to instantiate and abstract
telescopes.

We try to present a metaprogramming interface where reverted metavariables can
still be assigned to and have their original local contexts. It solves some
issues in Lean 4 (e.g. the `apply` tactic creates natural metavariables, since
they otherwise lead to elaboration failures if they're made the non-assignable
kind).

### `let` definitions

Local `let` definitions put stress on the abstraction that these `?m'`
metavariables are truly metavariables. To be more accurate, we have two kinds
of objects:

1. "root" metavariables `?m`, which have an associated type and a local context.

2. metavariable abstractions `?m' x₁ ... xₙ`, which have an associated
   metavariable `?m` and a list of `n` fvars in its local context that have been
   abstracted.

The "metavariable" `?m'` conventionally has a type and local context, but this
is not strictly necessary.

There is an important kind of scope linkage we want to work out for `let`
definitions. Consider `let x : t := f v; ?m`. We want to be able to later assign
`?m := g x` to construct the expression `let x : t := f v; g x`. Again, recall
that in this expression, `x` the free variable must become a De Bruijn variable.
We need to link the `let` binding expression itself to the local context's
`let` definition.

A simple but unsatisfactory solution is to not pass the linkage at all, and
instead zeta reduce the `let` definition, yielding `let x := f v; g (f v)`.
This is easy to do since the definition for `x` is contained in the local
context for `?m`, and so the zeta reduction can occur during metavariable
instantiation.

A subtlety that must be emphasized is that in a `let` expression, type
correctness is allowed to depend on the exact definition of `x`. Modeling
reversion of local variables using lambda functions fails (i.e., we can't
imagine that we are assigning a lambda function to `?m'`), since we cannot
encode the constraint that `x` is definitionally equal to what the local context
for `?m` says it is. For sake of argument, we would need a construct like
`fun_let x := v => ...` that is like `fun x => b` but which is only type correct
when applied to a value definitionally equal to `v`, with a corresponding
`pi_let x := v => ...` to represent its type. With these, we could
abstract `?m : T` in the example above, getting a metavariable
`?m' : pi_let x := v => T` with `?m := fun_let x := v => ?m' x`.

Lean 4 solves this by completely ignoring representability of delayed assignment
values. In this case, it will create `?m' : t → (let x := v; T)` and delay
assign `?m' x := ?m`. This assumes that `?m'` will only be applied to an `x`
that is definitionally equal to `f v`. (Note: at the time of writing,
`Meta.check` does not verify this. It is relatively easy to use a tactic like
`rw` to create a type-incorrect term! This only effects elaborator correctness
to be clear. The kernel, which does not deal in metavariables, catches the
error.) In general, one cannot use `?m' := fun x => ...` to assign `?m'` since
the body of such a function does not know that `x := v`.

A benefit to using function applications for metavariable abstractions is that
it takes no special effort to handle standard reductions. For example, zeta
reducing `let x := f v; ?m' x` yields `?m' (f v)`, and after instantiating
with the assignment `?m := g x` we get `g (f v)`. So, zeta reduction gives the
same result when applied before or after instantiation.

### Other details

- When abstracting a free variable `x` from `?m : T`, we need to recursively
  abstract `x` from any metavariables occuring in the type `T`, as well as from
  any metavariables in the local context of `?m`. This process terminates
  because abstraction creates metavariables with smaller local contexts. In
  particular, we can argue that it's possible to topologically sort "root"
  metavariables by well-foundedness of the metavariable context, that
  abstraction only modifies metavariable abstractions by adding abstracted free
  variables to their abstraction sets, and that the algorithm can proceed by
  visiting only accessible metavariables in topological order.

- Since metavariables can be referred to by name, and since elaboration can
  be postponed, it's possible to abstract a metavariable multiple times.
  For example, this abstracts `x` and `y` from `?m` in both orders, since
  `by` elaboration is postponed until after `fun` returns:
  ```
  fun x y; (?m, by let z := ?m; revert x; revert y; ...)
  ```
  LilLean handles this by maintaining "the" abstracted `?m` and monotonically
  increasing the set of abstracted free variables.

- (TBD) Once an abstracted metavariable is assigned, instantiation of abstracted
  assignments can be eager or lazy --- the best policy depends on the situation.
  Eager instantiation helps elaboration, but instantiation is unnecessary for
  proofs.

-/

public section

namespace LilLean

/--
The metavariable kind controls its unification behavior in `isDefEq`.
-/
inductive MetavarKind where
  /-- A plain metavariable. Can be assigned by unification. -/
  | natural
  /-- A metavariable that is not assignable by unification.
  (Called `syntheticOpaque` in Lean 4.) -/
  | opaque
  deriving BEq

/-
structure MetavarDecl where
  mvarId : MVarId
  /-- User-visible name. -/
  name : Name
  lctx : LocalContext
  type : ExprId
  kind : MetavarKind

inductive MetavarAssignment where
  /-- Simple assignment of a metavariable. The expression must be valid in the local context of the metavariable.
  When instantiating metavariables, simple assigments can be substituted immediately. -/
  | simple (e : ExprId)
  /-- Delayed abstraction assignment of a metavariable.
  If `lctx'` is the local context of the metavariable, then one must have `LocalContext.contains lctx' lctx fvars`.
  The expression must be valid in `lctx`.
  Substitution is delayed until all metavariables in `e` can be instantiated.
  At that point the substituted expression is `fun xs => e[fvars → xs]` with each fvar abstracted out of `e`
  (after all metavariables are instantiated). -/
  | delayed (lctx : LocalContext) (fvars : Array FVarId) (e : ExprId)

structure MetavarContext where
  decls : Lean.PersistentHashMap MVarId MetavarDecl
  assignments : Lean.PersistentHashMap MVarId MetavarAssignment

def MetavarContext.addDecl (mctx : MetavarContext) (decl : MetavarDecl) : MetavarContext :=
  { mctx with decls := mctx.decls.insert decl.mvarId decl }

partial def MetavarContext.instantiateMVars (mctx : MetavarContext) (e : Expr) : Expr :=
  let rec visit (e : Expr) : Expr :=
    match e with
    | .const .. | .sort .. | .fvar .. | .bvar .. => e
    | .lam binderName binderType body binderInfo =>
      .lam binderName (visit binderType) (visit body) binderInfo
    | .forallE binderName binderType body binderInfo =>
      .forallE binderName (visit binderType) (visit body) binderInfo
    | .letE binderName type value body =>
      .letE binderName (visit type) (visit value) (visit body)
    | .mvar mvarId =>
      match mctx.assignments.find? mvarId with
      | none => e
      | some (.simple e') => e'
      | some (.delayed lctx fvars e') =>
        let e' := visit e'
        if e'.hasExprMVar then
          e
        else
          fvars.foldr (init := e') fun fvar e' => lctx.mkBinding1 true fvar e' visit
    | .app .. =>
      let f := visit e.getAppFn
      let args := e.getAppArgs.map visit
      f.beta args
  visit e

--abbrev FVarIdSet :=

-- TODO deal with mvar contexts
/--
Given an fvar `fvarId`, gives an array (including `fvarId`) of the fvars in the local context
that depend on it, transitively, with respect to the metacontext.
-/
def MetavarContext.collectForwardDeps (mctx : MetavarContext) (lctx : LocalContext)
    (fvarId : FVarId) : Array FVarId :=
  let rec go (decls : List LocalDecl) : Array FVarId :=
    match decls with
    | [] => panic! "no such fvarid"
    | decl :: decls' =>
      if decl.fvarId == fvarId then
        #[fvarId]
      else
        let deps := go decls'
        match decl with
        | .cdecl fvarId' _ type _ =>
          if (mctx.instantiateMVars type).hasAnyFVar deps.contains then
            deps.push fvarId'
          else
            deps
        | .ldecl fvarId' _ type value =>
          if (mctx.instantiateMVars type).hasAnyFVar deps.contains then
            deps.push fvarId'
          else if (mctx.instantiateMVars value).hasAnyFVar deps.contains then
            deps.push fvarId'
          else
            deps
  go lctx.decls
  -- let i := lctx.decls.findIdx? (fun decl => decl.fvarId == fvarId) |>.get!

/--
Correctly abstracts `x` in `e`, even when `e` has metavariables with `x` in their local contexts.
-/
partial def MetavarContext.abstract1 (mctx : MetavarContext) (e : Expr) (x : FVarId) : MetavarContext × Expr :=
  sorry
-/

end LilLean
