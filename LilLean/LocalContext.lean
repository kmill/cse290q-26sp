/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Expr.Context

/-!
# Local contexts

This module defines local contexts.
-/

public section

namespace LilLean

inductive LocalDecl where
  /-- A local constant, representing a lambda binder or a pi binder. -/
  | protected cdecl (index : Nat) (fvarId : FVarId) (userName : Name)
      (type : ExprId) (binderInfo : BinderInfo)
  /-- A local `let` definition. -/
  | protected ldecl (index : Nat) (fvarId : FVarId) (userName : Name)
      (type value : ExprId)

def LocalDecl.index : LocalDecl → Nat
  | .cdecl index _ _ _ _ => index
  | .ldecl index _ _ _ _ => index

def LocalDecl.setIndex (decl : LocalDecl) (index : Nat) : LocalDecl :=
  match decl with
  | .cdecl _ fvarId userName type binderInfo =>
    .cdecl index fvarId userName type binderInfo
  | .ldecl _ fvarId userName type value =>
    .ldecl index fvarId userName type value

def LocalDecl.fvarId : LocalDecl → FVarId
  | .cdecl _ fvarId _ _ _ => fvarId
  | .ldecl _ fvarId _ _ _ => fvarId

def LocalDecl.userName : LocalDecl → Name
  | .cdecl _ _ userName _ _ => userName
  | .ldecl _ _ userName _ _ => userName

def LocalDecl.setUserName (decl : LocalDecl) (userName : Name) : LocalDecl :=
  match decl with
  | .cdecl index fvarId _ type binderInfo =>
    .cdecl index fvarId userName type binderInfo
  | .ldecl index fvarId _ type value =>
    .ldecl index fvarId userName type value

def LocalDecl.type : LocalDecl → ExprId
  | .cdecl _ _ _ type _ => type
  | .ldecl _ _ _ type _ => type

def LocalDecl.setType (decl : LocalDecl) (type : ExprId) : LocalDecl :=
  match decl with
  | .cdecl index fvarId userName _ binderInfo =>
    .cdecl index fvarId userName type binderInfo
  | .ldecl index fvarId userName _ value =>
    .ldecl index fvarId userName type value

def LocalDecl.binderInfo : LocalDecl → BinderInfo
  | .cdecl _ _ _ _ binderInfo => binderInfo
  | .ldecl _ _ _ _ _          => .explicit

def LocalDecl.setBinderInfo (decl : LocalDecl) (binderInfo : BinderInfo) : LocalDecl :=
  match decl with
  | .cdecl index fvarId userName type _ =>
    .cdecl index fvarId userName type binderInfo
  | .ldecl .. => decl

def LocalDecl.value? : LocalDecl → Option ExprId
  | .cdecl _ _ _ _ _     => none
  | .ldecl _ _ _ _ value => some value

def LocalDecl.setValue (decl : LocalDecl) (value : ExprId) : LocalDecl :=
  match decl with
  | .cdecl .. => decl
  | .ldecl index fvarId userName type _ =>
    .ldecl index fvarId userName type value

/--
A list of local declarations (`LocalDecl`s) for free variables (`FVarId`s).

In the locally nameless system, free variables index into the `LocalContext`,
and loose bvars are an error.
-/
structure LocalContext where
  /-- A list of declarations in the local context. They are optional so that
  declarations can be erased without needing to reindex them. -/
  decls : Lean.PersistentArray (Option LocalDecl) := {}
  /-- A map from fvarids to declarations. The declaration contains an `index`
  into `decls`. -/
  fvarIdToDecl : Lean.PersistentHashMap FVarId LocalDecl := {}
  deriving Inhabited

namespace LocalContext

/--
Gives the number of indices in use in the local context.
Can be used when detecting when a local context has been extended.
-/
def numIndices (lctx : LocalContext) : Nat :=
  lctx.decls.size

def getIndex? (lctx : LocalContext) (index : Nat) : Option LocalDecl :=
  lctx.decls[index]?.getD none

/--
Low-level function for extending the local context.
Assumes the free variable in `decl` is not already in the context.
-/
def addDecl (lctx : LocalContext) (decl : LocalDecl) :
    LocalContext :=
  assert! !lctx.fvarIdToDecl.contains decl.fvarId
  let index := lctx.decls.size
  let decl := decl.setIndex index
  { lctx with
    decls := lctx.decls.push decl
    fvarIdToDecl := lctx.fvarIdToDecl.insert decl.fvarId decl }

/--
Low-level function to add a new local constant to the context.
-/
def addCDecl (lctx : LocalContext)
    (fvarId : FVarId) (name : Name) (type : ExprId)
    (binderInfo : BinderInfo := .explicit) :
    LocalContext :=
  lctx.addDecl (.cdecl 0 fvarId name type binderInfo)

/--
Low-level function to add a new local `let` definition to the context.
-/
def addLDecl (lctx : LocalContext)
    (fvarId : FVarId) (name : Name) (type value : ExprId) :
    LocalContext :=
  lctx.addDecl (.ldecl 0 fvarId name type value)

def find? (lctx : LocalContext) (fvarId : FVarId) :
    Option LocalDecl :=
  lctx.fvarIdToDecl.find? fvarId

def contains (lctx : LocalContext) (fvarId : FVarId) : Bool :=
  lctx.fvarIdToDecl.contains fvarId

/-- Finds the last entry in the local context with the given name. -/
def findFromUserName? (lctx : LocalContext) (userName : Name) :
    Option LocalDecl :=
  lctx.decls.findSomeRev? fun
    | none => none
    | some decl => if decl.userName == userName then some decl else none

def usesUserName (lctx : LocalContext) (userName : Name) : Bool :=
  (lctx.findFromUserName? userName).isSome

def erase (lctx : LocalContext) (fvarId : FVarId) : LocalContext :=
  match lctx.find? fvarId with
  | none => lctx
  | some decl =>
    let decls := lctx.decls
    let decls :=
      if decls.size == decl.index + 1 then decls.pop
      else lctx.decls.set decl.index none
    { decls
      fvarIdToDecl := lctx.fvarIdToDecl.erase fvarId }

/--
Low-level function for updating the local context.
Assumes the new declaration is equivalent to the original, and the index and
fvarid are unmodified.
-/
def modifyLocalDecl (lctx : LocalContext) (fvarId : FVarId)
    (f : LocalDecl → LocalDecl) : LocalContext :=
  match lctx.find? fvarId with
  | none      => lctx
  | some decl =>
    let decl := f decl
    { decls        := lctx.decls.set decl.index decl
      fvarIdToDecl := lctx.fvarIdToDecl.insert decl.fvarId decl }

def setUserName (lctx : LocalContext) (fvarId : FVarId)
    (userName : Name) :
    LocalContext :=
  lctx.modifyLocalDecl fvarId (·.setUserName userName)

def setType (lctx : LocalContext) (fvarId : FVarId)
    (type : ExprId) :
    LocalContext :=
  lctx.modifyLocalDecl fvarId (·.setType type)

def setBinderInfo (lctx : LocalContext) (fvarId : FVarId)
    (binderInfo : BinderInfo) :
    LocalContext :=
  lctx.modifyLocalDecl fvarId (·.setBinderInfo binderInfo)

def setValue (lctx : LocalContext) (fvarId : FVarId)
    (value : ExprId) :
    LocalContext :=
  lctx.modifyLocalDecl fvarId (·.setValue value)

section Monad
variable {m : Type → Type} [Monad m] {β : Type}

def foldlM (lctx : LocalContext)
    (f : β → LocalDecl → m β) (init : β) (start : Nat := 0) :
    m β :=
  lctx.decls.foldlM (init := init) (start := start) fun b decl =>
    match decl with
    | none      => pure b
    | some decl => f b decl

def foldrM (lctx : LocalContext)
    (f : LocalDecl → β → m β) (init : β) :
    m β :=
  lctx.decls.foldrM (init := init) fun decl b =>
    match decl with
    | none      => pure b
    | some decl => f decl b

def findDeclM? (lctx : LocalContext)
    (f : LocalDecl → m (Option β)) :
    m (Option β) :=
  lctx.decls.findSomeM? fun decl =>
    match decl with
    | none      => pure none
    | some decl => f decl

def findDeclRevM? (lctx : LocalContext)
    (f : LocalDecl → m (Option β)) :
    m (Option β) :=
  lctx.decls.findSomeRevM? fun decl =>
    match decl with
    | none      => pure none
    | some decl => f decl

end Monad

/--
Returns true if every free variable in `lctx` (except those satisfying `except`)
are in `lctx'`.
-/
def subcontextOf (lctx lctx' : LocalContext)
    (except : FVarId → Bool := fun _ => false) :
    Bool :=
  lctx.decls.all fun
    | none => true
    | some decl =>
      if except decl.fvarId then
        true
      else
        lctx'.contains decl.fvarId

section MkBinding
variable {m : Type → Type} [Monad m] [MonadExprContext m]

/--
Low-level function for creating lambdas, pi types, and let expressions.
Does not abstract fvars from metavariables, nor does it instantiate
metavariables, neither in `b` nor in the local context.

If `usedLetOnly` is true (the default), then unused lets are eliminated.
-/
def mkBinding (lctx : LocalContext) (kind : BindingKind)
    (xs : Array FVarId) (b : ExprId) (usedLetOnly : Bool := true) :
    m ExprId := do
  let b ← exprAbstractFVarRev b xs
  xs.size.foldRevM (init := b) fun j _ b => do
    let x := xs[j]
    match lctx.find? x with
    | some (.cdecl _ _ n t i) =>
      let t ← exprAbstractFVarRev t xs (endIdx := j)
      kind.mk n t b i
    | some (.ldecl _ _ n t v) =>
      if ← pure (!usedLetOnly) <||> exprHasLooseBVarEq b 0 then
        let t ← exprAbstractFVarRev t xs (endIdx := j)
        let v ← exprAbstractFVarRev v xs (endIdx := j)
        mkExprLet n t v b
      else
        exprLiftLooseBVars b 1 (-1)
    | none => panic! "unknown free variable"

end MkBinding

end LocalContext

end LilLean
