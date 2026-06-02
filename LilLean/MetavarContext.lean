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
variables from expressions containing metavariables whose contexts depend on
those variables --- these are foundational algorithms for term elaboration, and
it is also somewhat subtle and technical.

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

The basic idea is we can create an auxiliary metavariable `?m'` with a function
type and with a local context not containing `x`, and then we can
assign `?m := ?m' x`. With this assignment, we can abstract `x` from `?m` and
construct the function expression ``.lam `x T (.app ?m' (.bvar 0)) .explicit``.
The key facts are (1) by *reverting* `x` to create `?m'`, we get a new
metavariable that no longer has `x` in scope and (2) the metavariable can still,
indirectly, depend on `x` since one can still assign a function to `?m'` that
makes use of this `.bvar 0` argument (note: this suggests that when
instantiating metavariable assignments, we ought to reduce any beta redexes
thus created).

Put another way, while `exprAbstractFVarRev` is able to abstract free variables
that are actually present in an expression, it is not able to take into account
any metavariable dependencies on free variables. We can create new metavariables
that "revert" these dependencies. Since this eliminates dependencies, it enables
`exprAbstractFVarRev` to correctly abstract free variables.

Note that in this scheme the lifetime of a metavariable ends once a free
variable it depends on is abstracted (and the metavariable appears in an
expression being abstracted as such). The exact local context does not survive.

For many uses of metavariables, this is OK. A metaprogram will enter the
telescope of a metavariable's type as needed, construct an expression, abstract,
assign, and repeat. One can imagine an extreme where metavariables are *only*
for the empty context, where all free variables are always fully abstracted,
not just the dependencies. This would be at a loss of efficiency however,
from all the telescope abstraction and instantiation overhead.

### Elaboration complications

This causes complications for metavariables that represent postponed
elaboration problems (e.g. tactics). For example, consider a goal `?g₁ : p → q`.
The `intro h` tactic operates by assigning `?g₁ := fun h : p => ?g₂`. If we
follow the reversion process described above, we would create `?g₂' : p → q`
and assign `?g₂ := ?g₂' h` to eliminate the dependence on `h : p`. However,
this completely defeats the purpose, since the new goal `?g₂'` has the exact
same type as what we started with!

We need a mechanism to preserve the local context at `?g₂` itself. The lifetime
of the local context needs to persist beyond the scope of `fun` itself.

In Lean 4, the concept of *delayed assignment* solves this problem. In a
delayed assignment, we create the metavariable `?g₂'` in the same way, but we
make the assignment "in reverse", as `?g₂' h := ?g₂`; the actual assignment is
delayed until `?g₂` is *fully assigned* (meaning `?g₂` contains no metavariables
once instantiated), and then, since this is a *Miller pattern*, this
higher-order unification has a unique solution `?g₂' x := ?g₁[h := x]` --- by
delaying until `?g₁` is fully assigned, `exprAbstractFVarRev` can correctly
abstract `h`. (Note that `?g₂'` doesn't get assigned to the lambda expression
`?g₂' := fun x => g₁[h := x]`. When there are `let` definitions, such an
expression might not even be type correct.)

Delayed assignment has some drawbacks. For one, the assignment does not occur
until the metavariable is fully assigned, which is a strong condition that can
lead to elaboration failures. For another, the delayed assigned metavariable
`?g₂'` is effectively unassignable. Normally we want to avoid assignment, since
it was found to lead to counterintuitive behavior if unification could assign
tactic metavariables during elaboration itself, but as part of the normal
operation of a tactic such unification can be desired.

LilLean takes a different approach, decoupling opacity from abstraction
behavior. The `MetavariableKind` records assignability of metavariables, and
abstraction works uniformly for all metavariables. Rather than assigning in
one direction or the other, it records that `?g₂' h ≟ ?g₂`, bidirectionally.
Once either metavariable is assigned, they are both assigned.
The assignment to `?g₂` may contain metavariables, and if it does, they
are abstracted without delay. (However, as an optimization we may consider not
instantiating opaque metavariables eagerly, but only when forced.) If `?g₂'` is
further abstracted, we abstract `?g₂` directly and assign `?g₂'`. Abstractions
don't form chains per se. One can think about this as being a lazy approach
to abstraction: we can imagine always abstracting `?g₂` fully, creating a
metavariable `?g₂'` with an empty local context. Such a metavariable does not
require further abstraction.

We try to present an interface where reverted metavariables can still be
assigned to and have their original local contexts. It solves some issues
in Lean 4 (e.g. the `apply` tactic creates natural metavariables, since they
otherwise lead to elaboration failures if they're made the non-assignable kind).

### `let` definitions

Local `let` definitions stress the abstraction that these `?m'` metavariables
are in fact metavariables.

There is a kind of scope linkage we want to work out for `let` definitions.
Consider `let x := f v; ?m`. We want to be able to later assign `?m := g x`
to construct `let x := f v; g x`, and we wish to avoid `let x := f v; g (f v)`.
The problem is that

It is straightforward to design things in such a way that we'd get the latter
zeta reduced version (e.g. )

a `?g₂'` metavariable

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
