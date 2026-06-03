import Batteries
import Mathlib.Logic.Equiv.Defs

/-!
# Elimination and recursion

Last time:
  We looked at inductive types
  and the elimination principles (recursors) that come with them

Today:
  How are elimination principles elaborated?
  How does unification work in `isDefEq`?
  How does `rw` work?
  How does structural recursion work?

-/

/-!
## Elaborating elimination principles

Some elimination principles are very easy:
-/
#check False.elim
#check Or.elim
example (n : Nat) (h : n = 1 ∨ n = 2) : n ≤ 2 :=
  Or.elim h sorry sorry
/-!
The type parameter return type is called the *motive*, since the choice of it
is "motivated" by the expected type (you figure it out via backwards reasoning).

> Conor McBride. "Elimination with a Motive." Types for Proofs and Programs.
> TYPES 2000. https://doi.org/10.1007/3-540-45842-5_13
-/

/-!
What is harder are elimination principles whose return type is an application
of the motive argument.
-/
#check Nat.rec
example (n : Nat) : n = 0 + n :=
  @Nat.rec (motive := fun n' => n' = 0 + n')
    rfl
    (fun _ h => congrArg Nat.succ h)
    n
/-!
This is a *higher-order unification* problem: we're solving for a
function/predicate. This is undecidable in general.
-/

/-!
### Aside: How does unification work?

We've glossed over `isDefEq` this quarter.

When there are no metavariables, definitional equality is roughly "reduce
subexpressions until the two sides are the same".

n : Nat ⊢ n + 2 ≟ (n + 1) + 1   by delta reduction of the LHS

There are heuristics to try to speed things up.
For example, lazy delta reduction uses

  Γ ⊢ a₁ ≟ b₁   ...   Γ ⊢ aₙ ≟ bₙ
  --------------------------------
  Γ ⊢ (f a₁ ... aₙ) ≟ (f b₁ ... bₙ)

and if that fails, it unfolds both sides. E.g. with the addition example,
it tries
  n : Nat ⊢ n ≟ n + 1   n : Nat ⊢ 2 ≟ 1
  -------------------------------------
  n : Nat ⊢ n + 2 ≟ (n + 1) + 1
but that fails, and then it unfolds +, which eventually succeeds.

Another rule,

Γ ⊢ t ≟ t'    Γ, x : t ⊢ b ≟ b'[x':=x]
------------------------------------------
Γ ⊢ (fun x : t => b) ≟ (fun x' : t' => b')


When there are _metavariables_, defeq reduces to problems of the form
  Γ ⊢ (?m a₁ ... aₙ) ≟ e
The goal is to find the *unique* solution for `?m`.

Every metavariable has a type and a local context.

1. e.g. n : Nat ⊢ (?m n) ≟ (0 + n = n)   where `?m` has an empty local context
2. e.g. n : Nat ⊢ (?m n) ≟ (0 + n = n)   where `?m` has `n : Nat` in its context

Both at least have this solution: ?m := fun n' => 0 + n' = n'.
Second has more solutions, e.g.
  ?m := fun n' => 0 + n = n
  ?m := fun n' => 0 + n' = n
  ?m := fun n' => 0 + n = n'
  ?m := fun n' => 0 + n' = n'

A *Miller pattern* is when `a₁ ... aₙ` are pairwise distinct free variables
not present in the context of `?m`. Miller patterns have unique solutions:
  ?m := fun x₁ ... xₙ => e[a₁:=x₁, ..., aₙ:=xₙ]

If n=0, this reduces to
  Γ ⊢ ?m ≟ e
which is straightforward, since this is a first-order unification.
So long as `?m` does not occur in `e` (in a suitable sense), we can
assign `?m := e`.

### Another approximation for higher-order unification

Suppose in
  Γ ⊢ (?m a₁ ... aₙ) ≟ e
that a₁, ..., aₙ are arbitrary expressions.

What we can do is find all occurrences of `aₙ` in `e` and abstract them,
giving `fun xₙ => e[aₙ:=xₙ]`, and then we proceed to `aₙ₋₁`, ..., eventually
giving `fun x₁ ... xₙ => e[aₙ:=xₙ,...,a₁:=x₁]`

e.g.
  Γ ⊢ ?m (n+1) ≟ n+1 > 0
then we use `?m := fun x => x > 0`.

This, it turns out, is how the elaborator solves for motives using expected
types.

This motive might not actually be type correct. ("Motive is not type correct.")


-/

/-!
## How does `rw` work?
-/
set_option pp.proofs true
#print Eq
#check Eq.rec

-- Manual `Eq.rec` applications to do rewriting

theorem myCongrArg {α β : Type} (f : α → β) (x x' : α) (h : x = x') :
    f x = f x' :=
  Eq.rec (motive := fun y _ => f x = f y) rfl h

theorem mkCongrFun {α : Type} {β : α → Type}
    (f f' : (x : α) → β x) (x : α) (h : f = f') :
    f x = f' x :=
  Eq.rec (motive := fun g _ => f x = g x) rfl h

def rewriteWith (α : Sort _) (lhs rhs : α) (t : lhs = rhs)
    (motive : α → Sort _) (h : motive rhs) : motive lhs :=
  Eq.rec h t.symm

/-
`my_rw foo`  rewrites using `foo : lhs = rhs`
-/
open Lean Elab Tactic in
elab "my_rw " thm:term : tactic => do
  withMainContext do
    let g ← getMainGoal
    let t ← Tactic.elabTerm thm none
    let (args, _, tTy) ← Meta.forallMetaTelescope (← Meta.inferType t)
    let t := mkAppN t args
    let tTy ← instantiateMVars tTy
    let some (α, lhs, rhs) := tTy.eq?
      | throwErrorAt thm "Expecting a proof of `lhs = rhs`"
    let gTy' ← Meta.kabstract (← g.getType) lhs
    let motive := Expr.lam `_a α gTy' .default
    unless ← Meta.isTypeCorrect motive do
      throwError "motive is not type correct{indentExpr motive}"
    let h ← Meta.mkFreshExprSyntheticOpaqueMVar (gTy'.instantiate1 rhs)
    let pf ← Meta.mkAppM ``rewriteWith #[α, lhs, rhs, t, motive, h]
    g.assign pf
    replaceMainGoal (h.mvarId! :: (args.map (·.mvarId!)).toList)

example (a b : Nat) : 1 + a + b = b + a + 1 := by
  my_rw Nat.add_assoc
  my_rw Nat.add_comm _ b
  my_rw Nat.add_comm 1
  rfl

example (a : Nat) (h : 0 < a) : a / a = 1 := by
  my_rw Nat.div_self
  rfl
  exact h

-- Using the app elaborator
example (a : Nat) (h : 0 < a) : a / a = 1 :=
  Eq.rec rfl (Nat.div_self h)

macro "my_rw'" thm:term : tactic =>
  `(tactic| refine' Eq.rec ?_ (Eq.symm ($thm ..)))

example (a : Nat) (h : 0 < a) : a / a = 1 := by
  my_rw' Nat.div_self
  exact h
  rfl



/-!
Some discussion after class:
-/

variable (motive : Nat → Sort _) in
#check Nat.below 4 = motive 3 ×' motive 2 ×' motive 1 ×' motive 0
#check Nat.brecOn

def tri (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => tri n' + (n' + 1)

#print tri
#check tri.eq_1
#print tri.eq_2
#print tri._sunfold
-- set_option smartUnfolding false
#check (id rfl : tri._sunfold 3 = _ + _)

def tri' (n : Nat) :=
  Nat.brecOn (motive := fun _ => Nat)
    n
    (fun n b =>
      match n with
      | 0 => 0
      | n' + 1 => b.1 + (n' + 1))

def fib (n : Nat) :=
  Nat.brecOn (motive := fun _ => Nat) n
    (fun n b =>
      match n with
      | 0 => 0
      | 1 => 1
      | n' + 2 => b.1 + b.2.1)
