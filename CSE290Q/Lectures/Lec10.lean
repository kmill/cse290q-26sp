import Lean

/-!
# Lean system overview

Goal: Understand the organization of Lean 4
system internals, and how they interoperate
to support its use as a *programming language*
and an *interactive theorem prover*.

-/

/-!
## Major components

- IO and runtime systems (memory management, etc.)
  - FBIP
- Core datatypes
  - `Lean.Level`
  - `Lean.Expr`
  - `Lean.LocalContext`
  - `Lean.Environment`
    - environment extensions
- Core interface
  - Basic state maintenance (configuration and the current
    environment) plus support for efficient backtracking of state
- Meta interface
  - Metavariable contexts, and dependency tracking
  - Type inference
  - Weak head normal form computation
  - Unification and definitional equality (convertibility) checking
  - Level constraint solving
  - Expression construction
    - applications
    - abstracting free variables to form lambdas and function types
  - Standard constructions (e.g. `noConfusion`)
  - "meta tactics" for low-level deduction rules
    - cases and induction
    - introduction rules
    - applying constructors and other functions/theorems
    - adding hypotheses
    - rewriting
  - "meta tactics" for higher-level automated reasoning
    - the simplification engine
    - the grind engine
- Elaborator interface
  - Macro system
    - Macro scopes and quasiquotations
  - Term elaboration
    - utilities for transforming `Lean.Syntax` into `Lean.Expr`
    - elaborators for built-in syntaxes
    - coercion system
    - typeclass system
    - postponement system
  - Tactic elaboration
    - metavariable and goal handling
    - elaborators for built-in tactics
  - Command elaboration
    - elaborators for built-in commands
    - `def`/`theorem`/`example`
    - `inductive`/`structure`
    - the attribute system
- Parser interface
  - Commands for defining and extending Lean's syntax
- Language Server Protocol (LSP) server
  - The Info system
  - RPC interfaces for responding to editor queries
  - InfoView
  - Proof widgets
- Pretty printer
  - Delaboration
  - Parenthesis insertion
  - Formatting
- Compiler
  - Transformations from elaborated declarations to IR
  - Optimizations
  - Transformaitons from IR to C code
- Kernel
  - Environment maintenance
  - Its own implementations in C++ of typechecking
- Lake, the build system

-/


/-!

### The approximate steps that Lean takes to process a file

1. Parsing.
   Read in the text of the file and convert it to `Syntax` objects.
   (Parentheses, operator precedence, etc.)

2. Macro expansion.
   Convert `Syntax` to simpler `Syntax` using macro definitions.

3. Elaboration.
   Convert `Syntax` to `Expr` objects, the "fully elaborated terms."

   A. Metavariables for implicit arguments and other pending terms
   B. Unification, as a consquence of "defeq" checks
   C. Tactic evaluation,
   D. Typeclass instance inference

   Elaboration generally tries to detect and report all errors.

4. Kernel typechecking.
   Fully elaborated terms are passed to the "kernel,"
   a small program whose sole purpose is checking the validity
   of definitions and proofs.

   The elaboration process is complex and ~~might~~ *does* have bugs.
   The kernel is only a couple thousand lines and has been much more
   carefully reviewed.

5. Compilation.
   Definitions that have computational content can be converted
   into runnable programs and either evaluated using an
   interpreter (what `#eval` uses) or compiled to C.

   Much of Lean 4 is written in Lean 4.

Other processes:

6. Pretty printing. ("Delaboration")
   Given an `Expr`, turn it back into a `Syntax` and then back
   into text. There are also inverses to macros, "application unexpanders,"
   which transform `Syntax` to `Syntax`.

   Pretty printing is used to show things in the Infoview.

7. Incremental and parallel elaboration.
   In conjunction with LSP, the Lean system tries to reuse
   work it has done, while you edit a file.
   The results are reported live in the editor.


-/


/-! ### Which is metaprogramming?

In a certain sense, *everything* that is done before kernel
typechecking is metaprogramming, writing programs that write programs.

We want to avoid writing terms ("programs") ourselves and
we want to be able to express ourselves in high-level proofs.

What we write serves as directives to Lean for how to actually
write the proof.

- We write convenient notations using macros
- We write elaborators that are good at filling in implicit arguments
- We write tactics to construct proof terms in an interactive way
- We write commands that automatically generate auxiliary definitions

Even the tactic scripts are a sort of metaprogram
(so writing tactics themselves can be regarded as metametaprogramming)

-/



/-! ### What's a fully elaborated term? -/

#check Lean.Syntax
#check Lean.Expr

-- Annotated and mildly simplified:
inductive Expr' where
  -- Variables bound by forall/fun, using de Bruijn indexing
  | bvar (deBruijnIndex : Nat)

  -- "Free" variables; to refer to local hypotheses in the current `LocalContext`.
  -- Used for elaboration, tactics, and typechecking algorithms.
  -- (These do not appear in fully elaborated terms.)
  | fvar (fvarId : FVarId)

  -- Metavariables; to be replaced by expressions assigned in the `MetavarContext`.
  -- Used by the elaborator to represent expressions that will be solved for later,
  -- for example implicit arguments, tactic proofs, postponed terms, etc.
  -- Unification can assign them.
  -- (These do not appear in fully elaborated terms.)
  | mvar (mvarId : MVarId)

  -- `Sort u`
  -- `Type u := Sort (u + 1)`
  | sort (u : Level)

  -- To refer to pre-existing theorems and definitions. The `Level`s
  -- instantiate the universe level variables for the constant.
  | const (declName : Name) (us : List Level)

  -- Applications of function arguments or theorem hypotheses
  -- For multiple arguments, nested: `.app (.app f x) y`
  | app (fn : Expr) (arg : Expr)

  -- "λ abstractions", i.e., functions and proofs-by-intro.
  | lam (binderName : Name) (binderType : Expr) (body : Expr)
        (binderInfo : BinderInfo)

  -- "Π types", i.e., (dependent) functions, for-alls, and implications
  | forallE (binderName : Name) (binderType : Expr) (body : Expr)
            (binderInfo : BinderInfo)

  -- `let x := v; b` for local definitions.
  -- Similar to `(fun x => b) v` but type-correctness of `b` can depend on the value of `x`.
  | letE (declName : Name) (type : Expr) (value : Expr) (body : Expr)

  -- Natural number literals and character strings
  | lit : Literal → Expr'

  -- Metadata attached to expressions, to direct elaboration
  | mdata (data : MData) (expr : Expr)

  -- Raw projections for "structure-like" inductive types
  | proj (typeName : Name) (idx : Nat) (struct : Expr)


/-! ### A bit of reflection -/

#eval toExpr true
#eval toExpr 37
#check 37

/-! ### The `theorem` command, elaborated -/

theorem mp {p q : Prop} (hp : p) (hpq : p → q) : q := hpq hp

theorem mp' : ∀ {p q : Prop}, p → (p → q) → q :=
  fun hp hpq ↦ hpq hp

theorem mp'_foralls :
    ∀ {p : Prop}, ∀ {q : Prop}, ∀ (_ : p), ∀ (_ : p → q), q :=
  @fun _ _ hp hpq ↦ hpq hp



def addMpDef (thmName : Name) : TermElabM Unit := do
  let stype ← `(∀ {p q : Prop}, p → (p → q) → q)
  let spf ← `(@fun _ _ hp hpq ↦ hpq hp)
  -- Elaborate the syntax for the type
  let type ← Term.elabTerm stype none
  -- Elaborate the syntax for the proof
  let pf ← Term.elabTermEnsuringType spf type
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
      (.lam `q (.sort (.succ .zero))
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
--  Meta.check pf
  -- Check that the type of `pf` is `type`
  unless ← Meta.isDefEq (← Meta.inferType pf) type do
    throwError "not defeq"
  -- Have the kernel check the theorem and add it to the environment
  addDecl <| Declaration.thmDecl
    { name := thmName
      levelParams := []
      type := type
      value := pf }

#eval addMpDef2 `mp'''
#print mp'''
set_option pp.proofs true
variable (h : 1 = 1) (motive : (n : Nat) → 1 = n → Type)
  (v : motive 1 h)
#check Eq.recOn (motive := motive) h v
#check Eq.recOn (motive := motive) (Eq.refl 1) v
#reduce Eq.recOn (motive := motive) (Eq.refl 1) v
#reduce Eq.recOn (motive := motive) h v
#check Acc.rec

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

/-
This is what the Lean elaborator does when it
sees `add_comm` by itself:
-/
def expandAddComm : TermElabM Expr := do
  let u ← mkFreshLevelMVar
  let G ← mkFreshExprMVar (some (.sort (.succ u)))
  let instTy : Expr := .app (.const ``AddCommMagma [u]) G
  let inst ← mkFreshExprMVar (some instTy)
  Term.registerSyntheticMVarWithCurrRef inst.mvarId! (.typeClass none)
  return .app (.app (.const ``add_comm [u]) G) inst

#eval expandAddComm

/--  A term elaborator to test `expandAddComm` -/
elab "mkAddCommExpr" : term => expandAddComm

#check mkAddCommExpr

#check mkAddCommExpr (1 : ℝ) 2

#check (mkAddCommExpr : ∀ (a b : ℝ), a + b = b + a)

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

- A table of `mvarId -> Expr` mappings for metavariables that
  have been assigned a value, potentially another metavariable.
  (The `instantiateMVars` command does the final replacement.)

- A table of `mvarId -> Expr` mappings for the type of each
  metavariable (which might themselves contain metavariables)

- A local context for each metavariable, which controls which
  `Expr.fvar`s are allowed when assigning a metavariable.

Hint: each goal in the Infoview *is* an unassigned metavariable.
Lean shows us the local context and type of each goal metavariable.

-/


/-!
## Tactic elaboration ingredients

The `by ...` notation has a term elaborator that sets up tactic mode.

Tactic mode consists of a list of metavariables called *goals*.

The `by ...` itself is replaced with a single metavariable, the
first goal to be proved.

Tactics are programs that manipulate the goals.

-/

example (p : Prop) : p → p := by
  sorry

example (p : Prop) : p → p := by
  intro h
  sorry

-- This is the same as...

example (p : Prop) : p → p := fun h => by
  sorry

example (p : Prop) : p → p := fun h => by
  exact h

-- This is the same as...

example (p : Prop) : p → p := fun h => h


elab "myIntro " nameStx:ident : tactic => do
  let name : Name := nameStx.getId
  let g : MVarId ← Tactic.getMainGoal
  g.withContext do
    let tgt : Expr ← g.getType'
    match tgt with
    | .forallE _ ty body bi =>
      withLocalDecl name bi ty fun arg => do
        let body' := body.instantiate1 arg
        let g' ← mkFreshExprSyntheticOpaqueMVar body'
        g.assign (← mkLambdaFVars #[arg] g')
        Tactic.replaceMainGoal [g'.mvarId!]
    | _ => throwError "Goal is not a forall/implication"

elab "myExact " t:term : tactic => do
  let g : MVarId ← Tactic.getMainGoal
  g.withContext do
    let tgt : Expr ← g.getType
    let e : Expr ← Term.elabTermEnsuringType t tgt
    g.assign e
    Tactic.replaceMainGoal []

theorem myThm (p : Prop) : p → p := by
  myIntro hp
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
