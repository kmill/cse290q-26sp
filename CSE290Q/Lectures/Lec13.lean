import Mathlib

/-!
# Lean system overview (continued'')

Goal: Understand the organization of Lean 4
system internals, and how they interoperate
to support its use as a *programming language*
and an *interactive theorem prover*.

-/

open Lean Meta Elab Term Tactic

/-! ### The `theorem` command, elaborated -/

theorem mp {p q : Prop} (hp : p) (hpq : p → q) : q := hpq hp

theorem mp' : ∀ {p q : Prop}, p → (p → q) → q :=
  fun hp hpq => hpq hp

theorem mp'_foralls :
    ∀ {p : Prop}, ∀ {q : Prop}, ∀ (_ : p), ∀ (_ : p → q), q :=
  @fun _ _ hp hpq => hpq hp


def addMpDef (thmName : Name) : TermElabM Unit := do
  let stype ← `(∀ {p q : Prop}, p → (p → q) → q)
  let spf ← `(@fun _ _ hp hpq ↦ hpq hp)
  -- Elaborate the syntax for the type
  let type ← Term.elabTerm stype none
  let type ← Term.ensureType type
  -- Elaborate the syntax for the proof
  let pf ← Term.elabTerm spf type
  let pf ← Term.ensureHasType type pf
  -- Complete the elaboration
  Term.synthesizeSyntheticMVarsNoPostponing
  -- Create a declaration
  let decl := Declaration.thmDecl
    { name := thmName
      levelParams := []
      type := ← instantiateMVars type
      value := ← instantiateMVars pf }
  -- Make sure it has no lingering metavariables
  Term.ensureNoUnassignedMVars decl
  -- Have the kernel check the theorem and add it to the environment
  addDecl decl

#eval addMpDef `mp''
#print mp''

set_option pp.raw true in #print mp''


def addMpDef2 (thmName : Name) : MetaM Unit := do
-- `(∀ {p q : Prop}, p → (p → q) → q)
  let type : Expr :=
    .forallE `p (.sort .zero)
      (.forallE `q (.sort .zero)
        (.forallE `hp (.bvar 1)
          (.forallE `hpq (.forallE `a (.bvar 2) (.bvar 2) .default)
            (.bvar 2)
            .default)
          .default)
        .implicit)
      .implicit
-- `(@fun _ _ hp hpq ↦ hpq hp)
  let pf : Expr :=
    .lam `p (.sort .zero)
      (.lam `q (.sort .zero)
        (.lam `hp (.bvar 1)
          (.lam `hpq (.forallE `a (.bvar 2) (.bvar 2) .default)
            (.app (.bvar 0) (.bvar 1))
            .default)
          .default)
        .implicit)
      .implicit
  -- Check that `type` is type correct
  Meta.check type
  -- Check that `pf` is type correct
  Meta.check pf
  -- Check that the type of `pf` is `type`
  unless ← Meta.isDefEq (← Meta.inferType pf) type do
    throwError "type of proof is{indentD (← Meta.inferType pf)}\n\
      but is expected to have type{indentD type}"
  -- Have the kernel check the theorem and add it to the environment
  addDecl <| Declaration.thmDecl
    { name := thmName
      levelParams := []
      type := type
      value := pf }

#eval addMpDef2 `mp'''
#print mp'''

-- Using the Meta interface
def addMpDef3 (thmName : Name) : MetaM Unit := do
  -- type = (∀ {p q : Prop}, p → (p → q) → q)
  -- pf = (@fun _ _ hp hpq ↦ hpq hp)
  let (type, pf) ←
    withLocalDecl `p .implicit (.sort .zero) fun p => do
      withLocalDecl `q .implicit (.sort .zero) fun q => do
        withLocalDecl `hp .default p fun hp => do
          -- let hpqTy ← mkForallFVars #[p] q   -- (p : _) → q
          let hpqTy ← mkForallFVars #[hp] q   -- (hp : p) → q
          withLocalDecl `hpq .default hpqTy fun hpq => do
            let type ← mkForallFVars #[p, q, hp, hpq] q
            let body := mkAppN hpq #[hp]
            let pf ← mkLambdaFVars #[p, q, hp, hpq] body
            pure (type, pf)
  logInfo m!"type = {type}"
  logInfo m!"pf = {pf}"
  -- Check that `type` is type correct
  Meta.check type
  -- Check that `pf` is type correct
  Meta.check pf
  -- Check that the type of `pf` is `type`
  unless ← Meta.isDefEq (← Meta.inferType pf) type do
    throwError "type of proof is{indentD (← Meta.inferType pf)}\n\
      but is expected to have type{indentD type}"
  -- Have the kernel check the theorem and add it to the environment
  addDecl <| Declaration.thmDecl
    { name := thmName
      levelParams := []
      type := type
      value := pf }
--set_option pp.raw true
#eval addMpDef3 `mp''''
#print mp''''

/-!
## Term elaboration ingredients

- Metavariables: holes in `Expr`s that the elaborator must solve for
- Unification: an algorithm to equate two `Expr`s
               (and assigning metavariables along the way)
- Term elaborators: programs to turn a `Syntax` into an `Expr`

-/

#check add_comm
#check (add_comm)
#check add_comm (1 : ℝ) 2
#check add_comm _ _
#check (add_comm _ _ : (1 : ℝ) + 2 = _ + _)

/-
This is what the Lean elaborator does when it
sees `add_comm` by itself:
-/
def expandAddComm : TermElabM Expr := do
  let u ← mkFreshLevelMVar
  let G ← mkFreshExprMVar (some (.sort (.succ u)))
  -- logInfo m!"u = {u}, G = {G}"
  let instTy : Expr := .app (.const ``AddCommMagma [u]) G
  let inst ← mkFreshExprMVar (some instTy)
  Term.registerSyntheticMVarWithCurrRef inst.mvarId! (.typeClass none)
  -- return .app (.app (.const ``add_comm [u]) G) inst
  return mkAppN (.const ``add_comm [u]) #[G, inst]

#check Expr.const

#eval expandAddComm

/--  A term elaborator to test `expandAddComm` -/
elab "mkAddCommExpr" : term => expandAddComm

#check mkAddCommExpr

#check mkAddCommExpr (1 : ℝ) 2

set_option trace.Meta.synthInstance true in
#check (mkAddCommExpr : ∀ (a b : ℝ), a + b = b + a)

-- (stopping point)

-- In this example, `thm`'s metavariables get solved for
-- due to `thm (1 : ℝ) 2`
#check
  let thm := mkAddCommExpr
  PProd.mk (thm (1 : ℝ) 2) thm
-- has type PProd (1 + 2 = 2 + 1) (∀ (a b : ℝ), a + b = b + a)



/-!
### What's a metavariable exactly?

Their full definition requires a few pieces:

- The `Expr.mvar` terms in an expression, representing holes

- An `MVarId`-to-`Expr` table for metavariables that
  have been assigned a value, potentially another metavariable.
  (The `instantiateMVars` command does the final replacement.)

- An `MVarId`-to-`Expr` table for the **type** of each
  metavariable (which might themselves contain metavariables)

- An `MVarId`-to-`LocalContext` table, which controls which
  `Expr.fvar`s are allowed when assigning to a metavariable.

Hint: each goal in the Infoview *is* an unassigned metavariable.
Lean shows us the local context and type of each goal metavariable.

  n : Nat               \
  m : Nat := n + 1      | local context
  h : n > 0             /
  ⊢ m > 1               type

(There are also universe level metavariables, with their own tables.)
-/
#check Expr.mvar
#check LocalContext
#check MetavarContext
#check instantiateMVars

/-!
## Tactic elaboration ingredients

The `by ...` notation is a term with an elaborator that sets up tactic mode.

Tactic mode consists of a list of metavariables called *goals*.

The `by ...` itself is replaced with a single metavariable, the
first goal to be proved.

Tactics are programs that manipulate the goals, by
1. assigning to goal metavariables, and
2. adding new metavariables to the goals list.

-/

example (p : Prop) : p → p := by
  intro h
  exact h

-- "operational semantics model"
-- `(by intro h; ... : p → q)`  =>  `fun h : p => (by ... : q)`
-- `(by exact t : p)` => `(t : p)`

example (p : Prop) : p → p := by
  intro h
  exact h
-- =>
example (p : Prop) : p → p := fun h : p => by
  exact h
-- =>
example (p : Prop) : p → p := fun h : p => h

-- "`refine` model"
-- recall that `refine` is like `exact`, but any `?_` placeholders in the term
-- become new goals
-- `intro h`  =>  `refine fun h => ?_`
-- `exact h`  =>  `refine h`
-- `by refine h` => `h`
-- `by refine (... ?_ ... ?_ ... ?_ ...); ...`  =>
--   `(... (by ...) ... (by ...) ... (by ...) ...)`

example (p : Prop) : p → p := by
  intro h
  exact h
-- =>
example (p : Prop) : p → p := by
  refine fun h => ?_
  refine h
-- =>
example (p : Prop) : p → p := fun h => (by refine h)
-- =>
example (p : Prop) : p → p := fun h => h

/-
Defining tactics using macros
-/
syntax "fun" term " =>": tactic
macro_rules
  | `(tactic| fun $t =>) => `(tactic| refine fun $t => ?_)

example (p : Prop) : p → p := by
  fun h =>
  exact h

-- that's `term` instead of `ident` since `fun` supports it!
example (p q : Prop) : (p ∧ q) → p := by
  fun ⟨h, _⟩ =>
  exact h

/--
`myIntro n` introduces a hypothesis into the local context.
-/
elab "myIntro " nameStx:ident : tactic => do
  let name : Name := nameStx.getId
  let g : MVarId ← Tactic.getMainGoal
  g.withContext do
    let tgt : Expr ← g.getType
    let tgt ← whnf tgt
    match tgt with
    | .forallE _ ty body bi =>
      withLocalDecl name bi ty fun arg => do
        let body' := body.instantiate1 arg
        let g' ← mkFreshExprSyntheticOpaqueMVar body'
        g.assign (← mkLambdaFVars #[arg] g')
        Tactic.replaceMainGoal [g'.mvarId!]
    | _ => throwError "Goal is not a forall/implication"

/--
`myExact t` closes the main goal using `t`
-/
elab "myExact " t:term : tactic => do
  let g : MVarId ← Tactic.getMainGoal
  g.withContext do
    let tgt : Expr ← g.getType
    let e : Expr ← Term.elabTermEnsuringType t tgt
    synthesizeSyntheticMVarsNoPostponing
    if ← occursCheck g e then
      g.assign e
    else
      throwError "{Expr.mvar g} occurs in {e}"
    Tactic.replaceMainGoal []

theorem myThm (p : Prop) : p → p := by
  myIntro hp
  -- refine ?foo
  -- myExact id ?foo
  myExact hp

#print myThm


-- What keeps tactics from giving bogus proofs?

elab "myBad" : tactic => do
  let g : MVarId ← Tactic.getMainGoal
  let v : Expr := toExpr 37
  g.assign v

example : 1 = 2 := by
  myBad


/-- Hard-coded `constructor` for a couple types. -/
elab "split_goal" : tactic =>
  Tactic.liftMetaTactic fun g => do
    let tgt ← g.getType'
    match tgt.getAppFn with
    | .const ``Iff _ =>
      g.apply (← mkConstWithFreshMVarLevels ``Iff.intro)
    | .const ``And _ =>
      g.apply (← mkConstWithFreshMVarLevels ``And.intro)
    | _ => throwError "Don't know how to handle this target type."

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  split_goal
  · assumption
  · assumption

-- This can be done mildly more inefficiently with a macro too.
macro "split_goal'" : tactic =>
  `(tactic|
      first
      | apply Iff.intro
      | apply And.intro
      | fail "Don't know how to handle this target.")

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  split_goal'
  · assumption
  · assumption
