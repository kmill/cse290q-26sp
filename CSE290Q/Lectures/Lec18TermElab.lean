import Lean
import CSE290Q.Lectures.Lec18TermElabSupport

/-!
# Let's build a simple term elaborator (part 4)

Goal:
  For a simplified Lean-like syntax for dependently type lambda calculus terms
  ("LilLean"), write a *term elaborator*, a function that converts that syntax
  into well-typed expressions.

Last time: implemented `elabAppFn` for function application elaboration.

TODO:
- eliminator support for `elabAppFn`
- `fun` elaboration, complete it
- `⟨...⟩` anonymous constructor elaboration
- creating a lil tactic system
- typeclass inference

-/

namespace LilLean

open Lean

namespace Parser
/-!
## Syntax definitions for terms
-/

/-- Represents a term of the LilLean language. -/
declare_syntax_cat lilterm

namespace LilTerm

/-
Special binding powers:
  lead := 1022
  arg := 1023
  max := 1024
-/

/-- Parentheses -/
syntax:max "(" lilterm ")" : lilterm

/-- Constants. Elaborates to either a local constant (from the local context)
or a global constant (from the environment). -/
syntax:max ident : lilterm

/-- Placeholders. Elaborates to a fresh metavariable. -/
syntax:max "_" : lilterm

/-- Numeric literals -/
syntax:max num : lilterm

/-- Applications -/
syntax:lead lilterm:max (ppSpace lilterm:arg)+ : lilterm

/-- Explicit annotation. For function applications, `@f x y z` means
to ignore explicit/implicit binder annotations in the type of `f`.
For functions, `@fun x y z => ...` means to ignore explicit/implicit binder
annotations in the expected type. -/
syntax:max "@" lilterm:max : lilterm

syntax explicitBinder := "(" ident (" : " lilterm)? ")"
syntax implicitBinder := "{" ident (" : " lilterm)? "}"
syntax instImplicitBinder := "[" lilterm "]"
syntax funBinder := ident <|> explicitBinder <|> implicitBinder <|> instImplicitBinder

-- completely different
--   p → q
--   (p : _) → q
-- completely the same
--   fun p => ...
--   fun (p : _) => ..

/-- Functions -/
syntax:max "fun " funBinder+ " => " lilterm : lilterm

/-- Arrows -/
syntax:25 lilterm:25 " → " lilterm:25 : lilterm

syntax piExplicitBinder := "(" ident " : " lilterm ")"
syntax piImplicitBinder := "{" ident " : " lilterm "}"
syntax piBinder := piExplicitBinder <|> piImplicitBinder <|> instImplicitBinder

/-- Dependent function types -/
syntax:25 piBinder " → " lilterm:25 : lilterm

/-- `let` definitions -/
syntax:lead "let " ident (" : " lilterm)? " := " lilterm "; " lilterm : lilterm

/-- Type universe -/
syntax "Type" : lilterm
/-- Prop universe -/
syntax "Prop" : lilterm

/-- Type ascriptions -/
syntax:max "(" lilterm " : " lilterm ")" : lilterm

/-- Apologize to LilLean for not knowing how to fill in this term yet. -/
syntax:max "lilsorry" : lilterm

/-- Represents a tactic of the LilLean language. -/
declare_syntax_cat liltactic

/-- Synthesizes a term using tactics. -/
syntax:lead "by " sepBy1IndentSemicolon(liltactic) : lilterm

end LilTerm

end Parser



namespace Elab.LilTerm
/-!
## Elaborator for terms
-/

inductive SyntheticMVarKind where
  | typeClass
  | tactic -- for future use

structure SyntheticMVarDecl where
  stx : Syntax
  kind : SyntheticMVarKind

structure Context where
  /-- When true, elaboration errors are logged, and `sorry` is used
  as a placeholder for terms that fail to elaborate. -/
  errToSorry : Bool := true

structure State where
  syntheticMVars : MVarIdMap SyntheticMVarDecl := {}
  pendingMVars : List MVarId := []

/--
LilTerm elaboration monad. Built on top of `MetaM` (for `isDefEq`, local
contexts, etc.), and keeps track of some additional state.
-/
abbrev TM := ReaderT Context (StateRefT State MetaM)

def throwUnknownSyntax {α : Type} : TM α :=
  throwError "Unknown syntax"

/--
Elaborates an identifier to either a local constant (an `Expr.fvar`)
or a global constant (an `Expr.const`).
-/
def elabConst (id : Ident) : TM Expr := do
  let result ← do
    let c := id.getId
    let lctx ← getLCtx
    let env ← getEnv
    if let some localDecl := lctx.findFromUserName? c then
      pure <| Expr.fvar localDecl.fvarId
    else if let some constVal := env.findConstVal? c.eraseMacroScopes then
      -- Instantiate the constant's universe levels with fresh
      -- level metavariables. (Like polytype instantiation in System F.)
      let us ← constVal.levelParams.mapM (fun _ => Meta.mkFreshLevelMVar)
      pure <| Expr.const constVal.name us
    else
      throwErrorAt id "Unknown constant `{c}`"
  -- Add an infotree node so LSP gives hover information
  Elab.Term.addTermInfo' id result |>.run'
  return result

/--
The data of a `piBinder` or `funBinder`.
-/
structure BinderView where
  ref : Syntax
  name : Name
  type? : Option Syntax
  info : BinderInfo

def elabPiBinder (binder : Syntax) : TM BinderView := do
  match binder with
  | `(Parser.LilTerm.piBinder| ($name : $ty)) =>
    return { ref := name, name := name.getId, type? := ty, info := .default }
  | `(Parser.LilTerm.piBinder| {$name : $ty}) =>
    return { ref := name, name := name.getId, type? := ty, info := .implicit }
  | `(Parser.LilTerm.piBinder| [$ty]) =>
    let instName ← Core.mkFreshUserName `inst
    return { ref := ty, name := instName, type? := ty, info := .instImplicit }
  | _ => withRef binder throwUnknownSyntax

def elabFunBinder (binder : Syntax) : TM BinderView := do
  match binder with
  | `(Parser.LilTerm.funBinder| $name:ident) =>
    return { ref := name, name := name.getId, type? := none, info := .default }
  | `(Parser.LilTerm.funBinder| ($name $[: $ty?]?)) =>
    return { ref := name, name := name.getId, type? := ty?, info := .default }
  | `(Parser.LilTerm.funBinder| {$name $[: $ty?]?}) =>
    return { ref := name, name := name.getId, type? := ty?, info := .implicit }
  | `(Parser.LilTerm.funBinder| [$ty]) =>
    let instName ← Core.mkFreshUserName `inst
    return { ref := ty, name := instName, type? := ty, info := .instImplicit }
  | _ => withRef binder throwUnknownSyntax

def elabSorry (expectedType? : Option Expr) (synthetic : Bool := false) :
    TM Expr := do
  let ty ← expectedType?.getDM Meta.mkFreshTypeMVar
  let u ← Meta.getLevel ty
  return mkApp2 (Expr.const ``sorryAx [u]) ty (toExpr synthetic)

/--
State for app elaboration.
-/
structure ElabAppFnState where
  /-- The resulting application. -/
  e : Expr
  /-- The type of `e` so far. -/
  eType : Expr
  /-- The unprocessed positional arguments. -/
  args : List Syntax
  /-- The expected type, if provided. Set to `none` once expected type
  propagation succeeds. -/
  expectedType? : Option Expr
  /--
  If the application's resulting type is of the form `aᵢ e₁ ... eₙ` where
  `aᵢ` is one of the arguments, then `motive?` is set to be the metavariable
  for this argument. This is a higher-order unification problem, and we use
  a certain approximation to solve for `aᵢ`.
  -/
  motive? : Option MVarId := none
  /-- When there is a `motive?`, collects additional elaborated arguments. -/
  extraArgs : Array Expr := #[]
  /-- Postponed arguments that need to be elaborated. These are accumulated
  in the event we find a `motive`. Any arguments whose expected type returns
  an application of the motive are postponed, since they are likely to serve
  as minor premises of a recursor-like application. -/
  postponed : Array (MVarId × Syntax) := #[]

abbrev AppM := StateRefT ElabAppFnState TM

inductive ResultingTypeResult where
  | none
  | type (t : Expr)
  /-- The application's return type is higher order and depends on this
  or a later argument. If `idx = 0` then it's this argument. -/
  | motive (idx : Nat)

def mkMotive (expectedType : Expr) (motiveArgs extraArgs : Array Expr) :
    MetaM Expr := do
  let expectedType ← instantiateMVars expectedType
  let expectedType ← extraArgs.foldrM (init := expectedType) fun arg expectedType => do
    let expectedType' ← Meta.kabstract expectedType (← instantiateMVars arg)
    let name ← Core.mkFreshUserName `x
    let argTy ← instantiateMVars (← Meta.inferType arg)
    return Expr.forallE name argTy expectedType' .default
  let expectedType ← motiveArgs.foldrM (init := expectedType) fun arg expectedType => do
    let expectedType' ← Meta.kabstract expectedType (← instantiateMVars arg)
    let name ← Core.mkFreshUserName `x
    let argTy ← instantiateMVars (← Meta.inferType arg)
    return Expr.lam name argTy expectedType' .default
  trace[LilLean.app] "computed motive{indentExpr expectedType}"
  unless (← Meta.isTypeCorrect expectedType) do
    throwError "failed to elaborate eliminator, motive is not type correct:\
      {indentD expectedType}"
  return expectedType

/--
Elaborates a function application `f args...` or `@f args...`

When `explicit := false` (no `@`), expands `args`, inserting metavariables
for implicit arguments.
Rule: implicit arguments are processed until the first explicit argument
that is not provided.

Additionally, the expected type is *propagated*.
Design constraints:
- We want propagation to *not* solve for arguments that have been explicitly
  provided, before those arguments are actually elaborated.
  Why? We want to be sure that the expressions obtained from elaboration
  match user expectations.
- If there are higher order unifications (`?m x y z =?= e`) we want it to be
  more likely for `x`, `y`, and `z` to have been elaborated already.
-/
partial def elabAppFnAux
    (elabLilTermEnsuringType : Syntax → Option Expr → TM Expr)
    (f : Expr) (args : Array Syntax)
    (expectedType? : Option Expr) (explicit : Bool) :
    TM Expr := do
  let fType ← Meta.inferType f
  loop |>.run' { e := f, eType := fType, args := args.toList, expectedType? }
where
  addArg (eTypeBody : Expr) (arge : Expr) : AppM Expr := do
    modify fun s =>
      { s with
        e := Expr.app s.e arge
        /-
        DTT: need to instantiate `bvar 0` with the argument.
        Also, use beta reducing instantiation since arguments might be higher
        order.
        -/
        eType := eTypeBody.instantiateBetaRevRange 0 1 #[arge] }
    loop
  elabAndAddArg (paramType eTypeBody : Expr) (arg : Syntax) : AppM Expr := do
    if let some motive := (← get).motive? then
      if (← Meta.forallTelescopeReducing paramType fun _ paramType' =>
            return paramType'.isApp && paramType'.getAppFn == .mvar motive) then
        let arge ← Meta.mkFreshExprSyntheticOpaqueMVar paramType
        trace[LilLean.app] "postponed argument `{arge}`"
        modify fun s => { s with postponed := s.postponed.push (arge.mvarId!, arg) }
        return ← addArg eTypeBody arge
    let arge ← elabLilTermEnsuringType arg paramType
    addArg eTypeBody arge
  processExplicit (paramType eTypeBody : Expr) : AppM Expr := do
    match (← get).args with
    | [] => finalize
    | arg::args' =>
      if arg.isOfKind ``Lean.Parser.Term.hole then
        -- If the argument is `_`, then override the kind to be implicit.
        modify fun s => { s with args := args' }
        processImplicit paramType eTypeBody
      else
        propagateExpectedType
        modify fun s => { s with args := args' }
        elabAndAddArg paramType eTypeBody arg
  processImplicit (paramType eTypeBody : Expr) : AppM Expr := do
    let arge ← Meta.mkFreshExprMVar paramType
    unless (← get).motive?.isSome || (← get).expectedType?.isNone do
      match ← resultingType? (← get).eType (← get).args 0 with
      | .motive 0 =>
        trace[LilLean.app] "motive argument: `{arge}`"
        let mvarId := arge.mvarId!
        -- Use synthetic opaque to avoid unification
        mvarId.setKind .syntheticOpaque
        modify fun s => { s with motive? := some mvarId }
      | _ => pure ()
    addArg eTypeBody arge
  loop : AppM Expr := do
    let eType' ← Meta.whnf (← get).eType
    if let .forallE paramName paramType eTypeBody paramInfo := eType' then
      trace[LilLean.app] m!"arg ({mkIdent paramName}, {repr paramInfo}): {paramType}"
      if paramInfo.isExplicit || explicit then
        processExplicit paramType eTypeBody
      else
        match paramInfo with
        | .implicit => processImplicit paramType eTypeBody
        | _ => throwError "no support for {repr paramInfo}"
    else
      match (← get).args with
      | arg::args' =>
        if (← get).motive?.isSome then
          -- Overapplied recursor. We will create a pi type motive.
          let arge ← elabLilTermEnsuringType arg none
          modify fun s =>
            { s with
              extraArgs := s.extraArgs.push arge
              args := args' }
          loop
        else
          throwError "have {(← get).args.length} argument(s), but not a function:\
            {indentExpr (← get).e}"
      | [] => finalize
  finalize : AppM Expr := do
    let mut e := (← get).e
    if let some expectedType := (← get).expectedType? then
      let eType ← Meta.inferType e
      if let some motive := (← get).motive? then
        let eType ← instantiateMVars (← Meta.whnf eType)
        if eType.isForall then
          throwError "eliminator application is underapplied:{indentExpr e}"
        assert! eType.getAppFn == .mvar motive
        let motiveArgs := eType.getAppArgs
        let extraArgs := (← get).extraArgs
        e := mkAppN e extraArgs
        trace[LilLean.app] "abstracting{indentD motiveArgs}\nand{indentD extraArgs}\nfrom\
          {indentExpr expectedType}\nto form motive"
        let motiveVal ← mkMotive expectedType motiveArgs extraArgs
        if (← occursCheck motive motiveVal) then
          motive.assign motiveVal
        else
          throwError "occurs check failed when assigning motive"
      else
        -- Hint for the type of `e` to be `expectedType`
        unless ← Meta.isDefEq eType expectedType do
          trace[LilLean.app] "final expected type propagation failed:\
            {indentExpr eType}\nand{indentExpr expectedType}"
    for (mvarId, arg) in (← get).postponed do
      let arge ← elabLilTermEnsuringType arg (← mvarId.getType)
      if (← occursCheck mvarId arge) then
        mvarId.assign arge
      else
        throwError "occurs check failed when assigning postponed argument"
    return e
  propagateExpectedType : AppM Unit := do
    let some expectedType := (← get).expectedType? | return
    if (← get).motive?.isSome then
      return
    match ← resultingType? (← get).eType (← get).args 0 with
    | .none => return
    | .type resultingType =>
      if ← Meta.isDefEq resultingType expectedType then
        trace[LilLean.app] "propagated expected type {expectedType}, \
          current expression is now{indentExpr (← get).e}"
        modify fun s => { s with expectedType? := none }
    | .motive _ => return
  /--
  Computes what the expected type of the function would be, without
  actually elaborating any of the arguments in `args`.
  The computation can fail if the result depends on the arguments.

  Looks to see if `eType` is of the form `(x : _) → ... → x e₁ ... eₙ`.
  If it is, then we consider `x` to be the "motive".

  The `eType` type may have loose bvars.
  -/
  resultingType? (eType : Expr) (args : List Syntax) (depth : Nat) :
      TM ResultingTypeResult := do
    let eType' ← if eType.hasLooseBVars then pure eType else Meta.whnf eType
    if let .forallE _ _paramType eTypeBody paramInfo := eType' then
      if paramInfo.isExplicit || explicit then
        match args with
        | [] => finalizeResultingType? eType [] depth
        | _::args' => resultingType? eTypeBody args' (depth + 1)
      else
        match paramInfo with
        | .implicit => resultingType? eTypeBody args (depth + 1)
        | _ => return .none
    else
      finalizeResultingType? eType args depth
  finalizeResultingType? (eType : Expr) (args : List Syntax) (depth : Nat) :
      TM ResultingTypeResult := do
    if eType.isApp && eType.getAppFn.isBVar then
      return .motive (depth - eType.getAppFn.bvarIdx! - 1)
    else if !args.isEmpty || eType.hasLooseBVars then
      return .none
    else
      return .type eType

mutual

/--
Elaborator for `lilterm` syntax. Frontend for `elabLilTermCore` that
handles the `errToSorry` feature.
-/
partial def elabLilTerm (t : Syntax) (expectedType? : Option Expr) :
    TM Expr := withRef t do
  withTraceNode `LilLean.app
      (fun _ => return m!"elabLilTerm{indentD t}") do
    trace[LilLean.app] "expected type: {expectedType?}"
    let result ←
      try
        elabLilTermCore t expectedType?
      catch ex =>
        if (← read).errToSorry then
          Elab.logException ex
          elabSorry expectedType? (synthetic := true)
        else
          throw ex
    trace[LilLean.app] "result:{indentD result}"
    -- Add an infotree node so LSP gives hover and expected type information
    Elab.Term.addTermInfo' t result expectedType? |>.run'
    return result

/--
Core elaborator for `lilterm` syntax.
-/
partial def elabLilTermCore (t : Syntax) (expectedType? : Option Expr) :
    TM Expr := withRef t do
  match t with
  | `(lilterm| ($t')) =>
    elabLilTerm t' expectedType?
  | `(lilterm| Type) =>
    return Expr.sort (Level.succ Level.zero)
  | `(lilterm| Prop) =>
    return Expr.sort Level.zero
  | `(lilterm| _) =>
    Meta.mkFreshExprMVar expectedType?
  | `(lilterm| lilsorry) =>
    elabSorry expectedType?
  | `(lilterm| ($t' : $ty)) =>
    let tyE ← elabLilTermType ty
    elabLilTermEnsuringType t' (some tyE)
  | `(lilterm| $n:num) =>
    let v := n.getNat
    return mkNatLit v
  | `(lilterm| $ty1 → $ty2) =>
    let ty1E ← elabLilTermType ty1
    let ty2E ← elabLilTermType ty2
    return Expr.forallE `_a ty1E ty2E .default
  | `(lilterm| $b:piBinder → $ty2) =>
    let view ← elabPiBinder b
    let dom ← elabLilTermType? view.type?
    Meta.withLocalDecl view.name view.info dom fun domFVar => do
      let ty2E ← elabLilTermType ty2
      Meta.mkForallFVars #[domFVar] ty2E
  | `(lilterm| fun $binders* => $body) =>
    let views ← binders.mapM elabFunBinder
    elabFun views body expectedType? (explicit := false)
  | `(lilterm| @fun $binders* => $body) =>
    let views ← binders.mapM elabFunBinder
    elabFun views body expectedType? (explicit := true)
  | `(lilterm| @$f:ident) =>
    let fe ← elabConst f
    elabAppFn fe #[] expectedType? (explicit := true)
  | `(lilterm| $f:ident) =>
    let fe ← elabConst f
    elabAppFn fe #[] expectedType? (explicit := false)
  | `(lilterm| @$f:ident $args*) =>
    let fe ← elabConst f
    elabAppFn fe args expectedType? (explicit := true)
  | `(lilterm| $f:ident $args*) =>
    let fe ← elabConst f
    elabAppFn fe args expectedType? (explicit := false)
  | `(lilterm| @$f:lilterm $args*) =>
    let fe ← elabLilTerm f none
    elabAppFn fe args expectedType? (explicit := true)
  | `(lilterm| $f:lilterm $args*) =>
    let fe ← elabLilTerm f none
    elabAppFn fe args expectedType? (explicit := false)
  | _ => throwUnknownSyntax

/--
Elaborates `t` and then ensures that its type is `expectedType?`, if given.
-/
partial def elabLilTermEnsuringType (t : Syntax) (expectedType? : Option Expr) :
    TM Expr := do
  let e ← elabLilTerm t expectedType?
  if let some expectedType := expectedType? then
    withTraceNode `LilLean.app (fun _ => return m!"ensuring {e} has type {expectedType}") do
      let eTy ← Meta.inferType e
      unless ← Meta.isDefEq eTy expectedType do
        throwErrorAt t "Term{indentExpr e}\n\
          has type{indentExpr eTy}\n\
          but is expected to have type{indentExpr expectedType}"
  return e

/--
Elaborates `t`, ensuring that the result is a type.
-/
partial def elabLilTermType (t : Syntax) : TM Expr := do
  let e ← elabLilTerm t none
  discard <| withRef t <| Meta.getLevel e
  return e

/--
Elaborates the type using `elabLilTermType`, if the type is present,
and otherwise returns a fresh type metavariable.
-/
partial def elabLilTermType? (t? : Option Syntax) : TM Expr := do
  if let some t := t? then
    elabLilTermType t
  else
    Meta.mkFreshTypeMVar

/--
Elaborates a `fun` expression.
Uses the expected type.

TODO: handle `explicit` and expected type binder infos.
-/
partial def elabFun (views : Array BinderView) (body : Syntax)
    (expectedType? : Option Expr) (explicit : Bool) :
    TM Expr := do
  loop #[] views.toList expectedType?
where
  loop (fvars : Array Expr) (views : List BinderView)
      (expectedType? : Option Expr) : TM Expr := do
    match views with
    | [] =>
      let e ← elabLilTerm body expectedType?
      Meta.mkLambdaFVars fvars e
    | view::views' =>
      let dom ← elabLilTermType? view.type?
      Meta.withLocalDecl view.name view.info dom fun fvar => do
        Elab.Term.addTermInfo' view.ref fvar (isBinder := true) |>.run'
        let expectedType?' ←
          if let some expectedType := expectedType? then
            let expectedType ← Meta.whnf expectedType
            if let .forallE _ t b _ := expectedType then
              if ← Meta.isDefEq dom t then
                pure <| some <| b.instantiate1 fvar
              else
                pure none
            else
              pure none
          else
            pure none
        loop (fvars.push fvar) views' expectedType?'

partial def elabAppFn
    (f : Expr) (args : Array Syntax)
    (expectedType? : Option Expr) (explicit : Bool) :
    TM Expr := do
  elabAppFnAux elabLilTermEnsuringType f args expectedType? explicit

end

end Elab.LilTerm

#reduce (types := true) IO Nat

#check let f := @id; (f true, f "yo")
#check let f := id; (f true, f "yo")

#check id id id id id id true

elab tk:"#elab_lilterm " t:lilterm : command => do
  Elab.Command.liftTermElabM do
    let e ← Elab.LilTerm.elabLilTerm t none |>.run {} |>.run' {}
    if e.hasSyntheticSorry then
      logInfoAt tk m!"elaborated with logged errors\n{e}"
    else
      logInfoAt tk m!"{e}"

#elab_lilterm Type
#elab_lilterm Prop
#elab_lilterm (Prop)
#elab_lilterm _
#elab_lilterm lilsorry
#elab_lilterm (lilsorry : Type)
#elab_lilterm 5
#elab_lilterm (_ : 5)
#elab_lilterm (Type : Type)
#elab_lilterm @id
#elab_lilterm id
#elab_lilterm id 5
#elab_lilterm (id (id 5) : Nat)
#elab_lilterm Type → Type
#elab_lilterm {p : Prop} → {q : Prop} → p → q → p
#elab_lilterm {p : Prop} → {q : Prop} → p → qq → p

#elab_lilterm (p : Type) → (q : Type) → p → q

#elab_lilterm (f : Nat → Type) → (n : Nat) → f n → f (Nat.add n 1)

#elab_lilterm fun (n : Nat) => Nat.succ n
#elab_lilterm fun {β : Type} => fun (x : β) => x
#elab_lilterm fun {β : Type} (x : β) => x

#elab_lilterm Bool.true 5

#check Nat.add
#check (fun n => Nat.rec rfl (fun n' h => congrArg Nat.succ h) n :
  (n : Nat) → Eq (Nat.add 0 n) n)

-- set_option trace.LilLean.app true

#elab_lilterm (fun n => Eq (Nat.add 0 n) n)

#elab_lilterm (fun n => Nat.rec rfl (fun n' h => congrArg Nat.succ h) n :
  (n : Nat) → Eq (Nat.add 0 n) n)
#elab_lilterm (fun n => Nat.recOn n rfl (fun n' h => congrArg Nat.succ h) :
  (n : Nat) → Eq (Nat.add 0 n) n)

def runTM {α} (x : Elab.LilTerm.TM α) : Elab.Term.TermElabM α :=
  x |>.run {} |>.run' {}

partial def Elab.LilTerm.elabFunBinders {α}
    (bs : List Syntax) (k : Array Expr → TM α) (xs : Array Expr := #[]) :
    TM α := do
  match bs with
  | [] => k xs
  | b::bs' =>
    let view ← elabFunBinder b
    let dom ← elabLilTermType? view.type?
    Meta.withLocalDecl view.name view.info dom fun x => do
      elabFunBinders bs' k (xs.push x)

elab tk:"lil_example " bs:Parser.LilTerm.funBinder* " : " ty:lilterm
    " := " body:lilterm : command => do
  Elab.Command.liftTermElabM <| runTM do
    Elab.LilTerm.elabFunBinders (Array.toList bs) fun xs => do
      let ty ← Elab.LilTerm.elabLilTermType? ty
      let body ← Elab.LilTerm.elabLilTerm body ty
      let e ← Meta.mkLambdaFVars xs body
      let eTy ← Meta.mkForallFVars xs ty
      if e.hasSyntheticSorry then
        logInfoAt tk m!"elaborated with logged errors\n\
          example : {eTy} :={indentExpr e}"
      else
        logInfoAt tk m!"example : {eTy} :={indentExpr e}"

lil_example (n : Nat) : Eq (Nat.add 0 n) n :=
  Nat.rec rfl (fun n' h => congrArg Nat.succ h) n

lil_example (n : Nat) : Eq (Nat.add 0 n) n :=
  Nat.rec rfl (fun n' h => congrArg Nat.succ h) n

def tri (n : Nat) :=
  match n with
  | 0 => 0
  | n' + 1 => tri n' + n

lil_example (n : Nat) (h : Eq (LilLean.tri n) 0) : Eq n 0 :=
  Nat.rec
    (fun h => h)
    (fun n' ih h => Nat.eq_zero_of_add_eq_zero_left h)
    n h -- overapplied with `h`, gets generalized

example (n : Nat) (h : Eq (LilLean.tri n) 0) : Eq n 0 := by
  induction n  --- `h` is auto-generalized
  sorry
  sorry

end LilLean
