/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Expr.Types
public import LilLean.Level.Basic

/-!
# Basic level constructions and functions
-/

public section

namespace LilLean

variable {ℓ ε : Type}

protected def Expr.eq [BEq ℓ] [BEq ε] (e e' : Expr ℓ ε) (alpha : Bool) : Bool :=
  match e, e' with
  | .bvar idx, .bvar idx' => idx == idx'
  | .fvar fvarId, .fvar fvarId' => fvarId == fvarId'
  | .mvar mvarId, .mvar mvarId' => mvarId == mvarId'
  | .sort u, .sort u' => u == u'
  | .const c us, .const c' us' =>
    c == c' && us.length == us'.length
    && (us.zip us').all fun (u, u') => u == u'
  | .app f a, .app f' a' => f == f' && a == a'
  | .lam n t b i, .lam n' t' b' i' =>
    (alpha || (n == n' && i == i')) && t == t' && b == b'
  | .pi n t b i, .pi n' t' b' i' =>
    (alpha || (n == n' && i == i')) && t == t' && b == b'
  | .let n t v b, .let n' t' v' b' =>
    (alpha || n == n') && t == t' && v == v' && b == b'
  | .lit l, .lit l' => l == l'
  | .proj t i s, .proj t' i' s' =>
    i == i' && t == t' && s == s'
  | _, _ => false

/-
Recall the structure of the hash, described in `MonadGetExpr.exprHash`:
- Bit 0 is 1 iff the expr has a level `param`.
- Bit 1 is 1 iff the expr has a level `mvar`.
- Bit 2 is 1 iff the expr has an `fvar`.
- Bit 3 is 1 iff the expr has an `mvar`.
- Bits 4-11 give the depth of the expression, saturated at 255
- Bits 12-31 give the range of loose bvars
- Bits 32-63 are the rest of the hash
-/

private structure ExprHashData where
  /-- bits 0-3 -/
  flags : UInt64 := 0
  /-- bits 4-11 -/
  approxDepth : UInt64 := 0
  /-- bits 12-31 -/
  looseBVarRange : Nat := 0
  /-- The full hash, bits 0-63, only bits 32-63 are used -/
  hash : UInt64

private def ExprHashData.decode (hash : UInt64) : ExprHashData where
  flags := hash &&& 15
  approxDepth := (hash >>> 4) &&& 255
  looseBVarRange := (hash.toUInt32 >>> 12).toNat
  hash := hash

private def ExprHashData.encode (data : ExprHashData) : UInt64 :=
  assert! (data.looseBVarRange >>> 20) == 0
  data.flags
    ||| (min data.approxDepth 255 <<< 4)
    ||| (data.looseBVarRange <<< 12).toUInt64
    ||| ((data.hash >>> 32) <<< 32)

private def ExprHashData.mkFlags
    (hasLevelParam hasLevelMVar hasFVar hasExprMVar : Bool := false) : UInt64 :=
  (if hasLevelParam then 1 else 0)
  ||| (if hasLevelMVar then 2 else 0)
  ||| (if hasFVar then 4 else 0)
  ||| (if hasExprMVar then 8 else 0)

private def ExprHashData.merge (data1 data2 : ExprHashData) : ExprHashData where
  flags := data1.flags ||| data2.flags
  approxDepth := max data1.approxDepth data2.approxDepth
  looseBVarRange := max data1.looseBVarRange data2.looseBVarRange
  hash := mixHash data1.hash data2.hash

def Expr.hashBVar (idx : Nat) : UInt64 :=
  ExprHashData.encode {
    looseBVarRange := idx + 1
    hash := mixHash 1 idx.toUInt64
  }

/--
Standard hash computation for expressions, given a function `getLevelHash` that
returns hashes for levels within `e` and `getExprHash` that returns hashes for
expressions within `e`.
-/
def Expr.hashCore (e : Expr ℓ ε)
    (getLevelHash : ℓ → UInt64)
    (getExprHash : ε → UInt64) : UInt64 :=
  match e with
  | .bvar idx =>
    Expr.hashBVar idx
  | .fvar fvarId =>
    ExprHashData.encode {
      flags := ExprHashData.mkFlags (hasFVar := true)
      hash := mixHash 2 (hash fvarId)
    }
  | .mvar mvarId =>
    ExprHashData.encode {
      flags := ExprHashData.mkFlags (hasExprMVar := true)
      hash := mixHash 3 (hash mvarId)
    }
  | .sort u =>
    let hu := getLevelHash u
    ExprHashData.encode {
      flags := hu &&& 3
      hash := mixHash 4 hu
    }
  | .const declName us =>
    let hus := us.foldl (init := 0) fun hus u =>
      let hu := getLevelHash u
      (mixHash hus hu &&& ~~~3) ||| ((hus ||| hu) &&& 3)
    ExprHashData.encode {
      flags := hus &&& 3
      hash := mixHash 5 <| mixHash (hash declName) hus
    }
  | .app fn arg =>
    let hfn := ExprHashData.decode (getExprHash fn)
    let harg := ExprHashData.decode (getExprHash arg)
    let data := hfn.merge harg
    ExprHashData.encode { data with
      approxDepth := data.approxDepth + 1
      hash := mixHash 6 data.hash }
  | .lam _ binderType body _ =>
    let hBinderType := ExprHashData.decode (getExprHash binderType)
    let hBody := ExprHashData.decode (getExprHash body)
    let hBody := { hBody with looseBVarRange := hBody.looseBVarRange - 1 }
    let data := hBinderType.merge hBody
    ExprHashData.encode { data with
      approxDepth := data.approxDepth + 1
      hash := mixHash 7 data.hash }
  | .pi _ binderType body _ =>
    let hBinderType := ExprHashData.decode (getExprHash binderType)
    let hBody := ExprHashData.decode (getExprHash body)
    let hBody := { hBody with looseBVarRange := hBody.looseBVarRange - 1 }
    let data := hBinderType.merge hBody
    ExprHashData.encode { data with
      approxDepth := data.approxDepth + 1
      hash := mixHash 8 data.hash }
  | .let _ type value body =>
    let hType := ExprHashData.decode (getExprHash type)
    let hValue := ExprHashData.decode (getExprHash value)
    let hBody := ExprHashData.decode (getExprHash body)
    let hBody := { hBody with looseBVarRange := hBody.looseBVarRange - 1 }
    let data := hType.merge (hValue.merge hBody)
    ExprHashData.encode { data with
      approxDepth := data.approxDepth + 1
      hash := mixHash 9 data.hash }
  | .lit v =>
    ExprHashData.encode { hash := mixHash 10 <| hash v }
  | .proj typeName idx struct =>
    let hStruct := ExprHashData.decode (getExprHash struct)
    ExprHashData.encode { hStruct with
      approxDepth := hStruct.approxDepth + 1
      hash := mixHash 10 <| mixHash (hash typeName) <| mixHash (hash idx) hStruct.hash }

instance [Hashable ℓ] [Hashable ε] : Hashable (Expr ℓ ε) where
  hash e := Expr.hashCore e hash hash

/--
Applies `f` and `g` to (non-recursively) update handles.
The `g` function gets additional information about the De Bruijn depth.
-/
def Expr.mapDepth {ℓ ℓ' ε ε'} (f : ℓ → ℓ') (g : ε → Nat → ε')
    (e : Expr ℓ ε) (depth : Nat) : Expr ℓ' ε' :=
  match e with
  | .bvar idx => .bvar idx
  | .fvar fvarId => .fvar fvarId
  | .mvar mvarId => .mvar mvarId
  | .sort u => .sort (f u)
  | .const declName us => .const declName (us.map f)
  | .app fn arg => .app (g fn depth) (g arg depth)
  | .lam n t b i => .lam n (g t depth) (g b (depth + 1)) i
  | .pi n t b i => .pi n (g t depth) (g b (depth + 1)) i
  | .let n t v b => .let n (g t depth) (g v depth) (g b (depth + 1))
  | .lit l => .lit l
  | .proj t i s => .proj t i (g s depth)

def Expr.map {ℓ ℓ' ε ε'} (f : ℓ → ℓ') (g : ε → ε')
    (e : Expr ℓ ε) : Expr ℓ' ε' :=
  Expr.mapDepth f (fun e' _ => g e') e 0

instance : Functor (Expr ℓ) where
  map := Expr.map id

def ExprGetter.mkExpr' (ctx : ExprGetter ℓ ε) (e : ε) (alpha : Bool := false) :
    Expr' ctx alpha :=
  { handle := e }

namespace Expr'
variable {alpha : Bool} {ctx : ExprGetter ℓ ε}
variable (e e' : Expr' ctx alpha)

def get : Expr (Level' ctx.level) (Expr' ctx alpha) :=
  Expr.map ctx.mkLevel' (ctx.mkExpr' · alpha) (ctx.getExpr e.handle)

def hash : UInt64 := ctx.exprHash e.handle

/--
Returns true if the expression contains a level parameter.
-/
def hasLevelParam : Bool := e.hash &&& 1 > 0

/--
Returns true if the expression contains a level metavariable.
(Note: true even if the metavariable is assigned.)
-/
def hasLevelMVar : Bool := e.hash &&& 2 > 0

/--
Returns true if the expression contains an fvar.
-/
def hasFVar : Bool := e.hash &&& 4 > 0

/--
Returns true if the expression contains an expression mvar.
(Note: true even if the metavariable is assigned.)
-/
def hasExprMVar : Bool := e.hash &&& 8 > 0

/--
Returns true if the expression contains a level or expression mvar.
(Note: true even if the metavariable is assigned.)
-/
def hasMVar : Bool := e.hasLevelMVar || e.hasExprMVar

/--
Returns the depth of recursion of the expression, saturated at 255.
-/
def approxDepth : Nat :=
  (ExprHashData.decode e.hash).approxDepth.toNat

/--
Returns the (exclusive) upper bound for loose bvars appearing in the expression.
For example, the loose bvar range for `.bvar 2` is `3`, and the loose bvar
range for `.const ..` is `0`.
-/
def looseBVarRange : Nat :=
  (ExprHashData.decode e.hash).looseBVarRange

/--
Returns true if the expression contains a loose bvar (i.e. if it is not
locally closed).
-/
def hasLooseBVars : Bool :=
  e.looseBVarRange > 0

/--
Returns `true` if `u` and `v` are structurally equal.
If `alpha` is true, then ignores binder names and binder info.
This implements the `BEq` instance for `Expr'`.
-/
protected partial def eq [BEq ℓ] [BEq ε] (e e' : Expr' ctx alpha) : Bool :=
  let : BEq (Expr (Level' ctx.level) (Expr' ctx alpha)) :=
    let : BEq (Expr' ctx alpha) := ⟨Expr'.eq⟩
    ⟨Expr.eq (alpha := alpha)⟩
  if e.handle == e'.handle then
    true
  else if e.hash != e'.hash then
    -- Note: we are relying on the fact that the hash function ignores
    -- binder names and binder info.
    false
  else
    e.get == e'.get

instance [BEq ℓ] [BEq ε] : BEq (Expr' ctx alpha) where
  beq := Expr'.eq

end Expr'

section Accessors
variable {ctx : ExprGetter ℓ ε} {alpha : Bool}

partial def Expr'.getAppNumArgs (e : Expr' ctx alpha) : Nat :=
  go e 0
where
  go (e : Expr' ctx alpha) (acc : Nat) : Nat :=
    match e.get with
    | .app f _ => go f (acc + 1)
    | _ => acc

private partial def Expr'.withRevAppAux {α} [Inhabited α]
    (e : Expr' ctx alpha) (revArgs : Array (Expr' ctx alpha))
    (k : Expr' ctx alpha → Array (Expr' ctx alpha) → α) : α :=
  match e.get with
  | .app f a => withRevAppAux f (revArgs.push a) k
  | _ => k e revArgs

partial def Expr'.withRevApp {α} [Inhabited α] (e : Expr' ctx alpha)
    (k : Expr' ctx alpha → Array (Expr' ctx alpha) → α) : α :=
  withRevAppAux e #[] k

partial def Expr'.withApp {α} [Inhabited α] (e : Expr' ctx alpha)
    (k : Expr' ctx alpha → Array (Expr' ctx alpha) → α) : α :=
  withRevAppAux e #[] fun f revArgs => k f revArgs.reverse

partial def Expr'.getAppFn (e : Expr' ctx alpha) : Expr' ctx alpha :=
  match e.get with
  | .app f _ => f.getAppFn
  | _ => e

partial def Expr'.getAppRevArgs (e : Expr' ctx alpha) :
    Array (Expr' ctx alpha) :=
  e.withRevApp fun _ revArgs => revArgs

partial def Expr'.getAppArgs (e : Expr' ctx alpha) :
    Array (Expr' ctx alpha) :=
  e.withApp fun _ args => args

end Accessors

section
variable {m : Type → Type} [Monad m]

/--
Applies `f` and `g` to (non-recursively) update handles.
The `g` function gets additional information about the De Bruijn depth.
-/
def Expr.mapDepthM {ℓ ℓ' ε ε'} (f : ℓ → m ℓ') (g : ε → Nat → m ε')
    (e : Expr ℓ ε) (depth : Nat) : m (Expr ℓ' ε') := do
  match e with
  | .bvar idx => return .bvar idx
  | .fvar fvarId => return .fvar fvarId
  | .mvar mvarId => return .mvar mvarId
  | .sort u => return .sort (← f u)
  | .const declName us => return .const declName (← us.mapM f)
  | .app fn arg => return .app (← g fn depth) (← g arg depth)
  | .lam n t b i => return .lam n (← g t depth) (← g b (depth + 1)) i
  | .pi n t b i => return .pi n (← g t depth) (← g b (depth + 1)) i
  | .let n t v b => return .let n (← g t depth) (← g v depth) (← g b (depth + 1))
  | .lit l => return .lit l
  | .proj t i s => return .proj t i (← g s depth)

def Expr.mapM (f : ℓ → m ℓ) (g : ε → m ε)
    (e : Expr ℓ ε) : m (Expr ℓ ε) :=
  Expr.mapDepthM f (fun e' _ => g e') e 0

section
variable [MonadGetExpr m ℓ ε]

def exprHasLevelParam (e : ε) : m Bool := do
  return (← getExprGetter).mkExpr' e |>.hasLevelParam

def exprHasLevelMVar (e : ε) : m Bool := do
  return (← getExprGetter).mkExpr' e |>.hasLevelMVar

def exprHasFVar (e : ε) : m Bool := do
  return (← getExprGetter).mkExpr' e |>.hasFVar

def exprHasExprMVar (e : ε) : m Bool := do
  return (← getExprGetter).mkExpr' e |>.hasExprMVar

def exprHasMVar (e : ε) : m Bool := do
  return (← getExprGetter).mkExpr' e |>.hasMVar

def exprApproxDepth (e : ε) : m Nat := do
  return (← getExprGetter).mkExpr' e |>.approxDepth

def exprLooseBVarRange (e : ε) : m Nat := do
  return (← getExprGetter).mkExpr' e |>.looseBVarRange

def exprHasLooseBVars (e : ε) : m Bool := do
  return (← getExprGetter).mkExpr' e |>.hasLooseBVars

/--
Returns `true` if `u` and `v` are structurally equal.

If `alpha` is true, then ignores binder names and binder info.
-/
partial def exprEq [BEq ℓ] [BEq ε] (e e' : ε) (alpha : Bool := false) :
    m Bool := do
  let ctx ← getExprGetter
  return ctx.mkExpr' e alpha == ctx.mkExpr' e' alpha

/--
Returns `true` if `u` and `v` are structurally equal while ignoring binder
names and binder info. This is a wrapper around `exprEq (alpha := true)`.
-/
partial def exprEquiv [BEq ℓ] [BEq ε] (e e' : ε) : m Bool :=
  exprEq e e' (alpha := true)

partial def exprGetAppNumArgs (e : ε) : m Nat :=
  return (← getExprGetter).mkExpr' e |>.getAppNumArgs

partial def exprWithRevApp {α} [Inhabited α] (e : ε)
    (k : ε → Array ε → m α) : m α := do
  (← getExprGetter).mkExpr' e |>.withRevApp fun f revArgs =>
    k f.handle (revArgs.map (·.handle))

partial def exprWithApp {α} [Inhabited α] (e : ε)
    (k : ε → Array ε → m α) : m α := do
  (← getExprGetter).mkExpr' e |>.withApp fun f args =>
    k f.handle (args.map (·.handle))

partial def exprGetAppFn (e : ε) : m ε :=
  return (← getExprGetter).mkExpr' e |>.getAppFn.handle

partial def exprGetAppRevArgs (e : ε) : m (Array ε) :=
  return (← getExprGetter).mkExpr' e |>.getAppRevArgs |>.map (·.handle)

partial def exprGetAppArgs (e : ε) : m (Array ε) :=
  return (← getExprGetter).mkExpr' e |>.getAppArgs |>.map (·.handle)

section
variable [MonadMkExpr m ℓ ε]

def mkExprBVar (idx : Nat) : m ε := mkExpr (.bvar idx)

def mkExprFVar (fvarId : FVarId) : m ε := mkExpr (.fvar fvarId)

def mkExprMVar (mvarId : MVarId) : m ε := mkExpr (.mvar mvarId)

def mkExprSort (u : ℓ) : m ε := mkExpr (.sort u)

def mkExprConst (declName : Name) (us : List ℓ) : m ε :=
  mkExpr (.const declName us)

def mkExprApp (fn : ε) (arg : ε) : m ε := mkExpr (.app fn arg)

def mkExprAppN (f : ε) (args : Array ε) : m ε :=
  args.foldlM (init := f) mkExprApp

def mkExprLam (binderName : Name) (binderType : ε) (body : ε)
    (binderInfo : BinderInfo) : m ε :=
  mkExpr (.lam binderName binderType body binderInfo)

def mkExprPi (binderName : Name) (binderType : ε) (body : ε)
    (binderInfo : BinderInfo) : m ε :=
  mkExpr (.pi binderName binderType body binderInfo)

def mkExprLet (declName : Name) (type : ε) (value : ε) (body : ε) : m ε :=
  mkExpr (.let declName type value body)

def mkExprLit (l : Literal) : m ε := mkExpr (.lit l)

def mkExprProj (typeName : Name) (idx : Nat) (struct : ε) : m ε :=
  mkExpr (.proj typeName idx struct)

/--
Represents the choice of either an `Expr.lam` or `Expr.pi` constructor.
The motivation is that many constructions work for both lambda expressions
and pi types.
-/
inductive BindingKind
  | lam
  | pi

/--
Constructs either an `Expr.lam` or `Expr.pi` depending on the `kind`.
-/
def BindingKind.mk (kind : BindingKind)
    (binderName : Name) (binderType : ε) (body : ε) (binderInfo : BinderInfo) :
    m ε :=
  match kind with
  | .lam => mkExprLam binderName binderType body binderInfo
  | .pi => mkExprPi binderName binderType body binderInfo

end

section Update
variable [MonadMkExpr m ℓ ε] [BEq ℓ] [BEq ε]

def updateExprSort (orig : ε) (newU : ℓ) : m ε := do
  if let .sort u ← getExpr orig then
    if u == newU then
      return orig
  mkExprSort newU

def updateExprConst (orig : ε) (newDeclName : Name) (newUs : List ℓ) : m ε := do
  if let .const declName us ← getExpr orig then
    if declName == newDeclName && us == newUs then
      return orig
  mkExprConst newDeclName newUs

def updateExprApp (orig : ε) (newFn newArg : ε) : m ε := do
  if let .app fn arg ← getExpr orig then
    if fn == newFn && arg == newArg then
      return orig
  mkExprApp newFn newArg

def updateExprLam (orig : ε) (newBinderName : Name)
    (newBinderType newBinderBody : ε) (newBinderInfo : BinderInfo) : m ε := do
  if let .lam binderName binderType binderBody binderInfo ← getExpr orig then
    if binderName == newBinderName && binderType == newBinderType
        && binderBody == newBinderBody && binderInfo == newBinderInfo then
      return orig
  mkExprLam newBinderName newBinderType newBinderBody newBinderInfo

def updateExprPi (orig : ε) (newBinderName : Name)
    (newBinderType newBinderBody : ε) (newBinderInfo : BinderInfo) : m ε := do
  if let .pi binderName binderType binderBody binderInfo ← getExpr orig then
    if binderName == newBinderName && binderType == newBinderType
        && binderBody == newBinderBody && binderInfo == newBinderInfo then
      return orig
  mkExprPi newBinderName newBinderType newBinderBody newBinderInfo

def updateExprLet (orig : ε) (newDeclName : Name)
    (newType newValue newBody : ε) : m ε := do
  if let .let declName type value body ← getExpr orig then
    if declName == newDeclName && type == newType && value == newValue
        && body == newBody then
      return orig
  mkExprLet newDeclName newType newValue newBody

def updateExprProj (orig : ε) (newTypeName : Name) (newIdx : Nat)
    (newStruct : ε) : m ε := do
  if let .proj typeName idx struct ← getExpr orig then
    if typeName == newTypeName && idx == newIdx && struct == newStruct then
      return orig
  mkExprProj newTypeName newIdx newStruct

/--
Applies `f` and `g` to (non-recursively) update level and expression handles,
returning the original expression if possible.
-/
def exprMapDepthM (f : ℓ → m ℓ) (g : ε → Nat → m ε)
    (e : ε) (depth : Nat) : m ε := do
  match (← getExpr e) with
  | .bvar _ => return e
  | .fvar _ => return e
  | .mvar _ => return e
  | .sort u => updateExprSort e (← f u)
  | .const declName us => updateExprConst e declName (← us.mapM f)
  | .app fn arg => updateExprApp e (← g fn depth) (← g arg depth)
  | .lam n t b i => updateExprLam e n (← g t depth) (← g b (depth + 1)) i
  | .pi n t b i => updateExprPi e n (← g t depth) (← g b (depth + 1)) i
  | .let n t v b => updateExprLet e n (← g t depth) (← g v depth) (← g b (depth + 1))
  | .lit _ => return e
  | .proj t i s => updateExprProj e t i (← g s depth)

/--
Applies `g` to (non-recursively) update expression handles,
returning the original expression if possible.
-/
def exprMapDepthM' (g : ε → Nat → m ε) (e : ε) (depth : Nat) : m ε := do
  match (← getExpr e) with
  | .bvar _ => return e
  | .fvar _ => return e
  | .mvar _ => return e
  | .sort _ => return e
  | .const _ _ => return e
  | .app fn arg => updateExprApp e (← g fn depth) (← g arg depth)
  | .lam n t b i => updateExprLam e n (← g t depth) (← g b (depth + 1)) i
  | .pi n t b i => updateExprPi e n (← g t depth) (← g b (depth + 1)) i
  | .let n t v b => updateExprLet e n (← g t depth) (← g v depth) (← g b (depth + 1))
  | .lit _ => return e
  | .proj t i s => updateExprProj e t i (← g s depth)

end Update

end

section ReplaceExpr
variable [MonadGetExpr m ℓ ε] [MonadMkExpr m ℓ ε]

/--
Caches for `exprReplace`.
-/
private structure ReplaceState
    (ℓ ε : Type) [BEq ℓ] [Hashable ℓ] [BEq ε] [Hashable ε] where
  levels : Std.HashMap ℓ (Option ℓ) := {}
  exprs : Std.HashMap (ε × Nat) (Option ε) := {}
  deriving Inhabited

/--
Replaces subexpressions in `e` using `f` and `g`. The functions return `none` if
the children should be visited.
The function is given the current De Bruijn depth.
Caches results by handle, so it's able to preserve sharing.
-/
partial def exprReplaceDepth [BEq ℓ] [Hashable ℓ] [BEq ε] [Hashable ε]
    (f : ℓ → m (Option ℓ)) (g : ε → Nat → m (Option ε))
    (e : ε) (depth : Nat) : m ε :=
  goExpr e depth |>.run' {}
where
  getf (u : ℓ) : StateT (ReplaceState ℓ ε) m (Option ℓ) := do
    if let some u'? := (← get).levels[u]? then
      return u'?
    else
      let u'? ← f u
      modify fun s => { s with levels := s.levels.insert u u'? }
      return u'?
  getg (e : ε) (depth : Nat) :
      StateT (ReplaceState ℓ ε) m (Option ε) := do
    if let some e'? := (← get).exprs[(e, depth)]? then
      return e'?
    else
      let e'? ← g e depth
      modify fun s => { s with exprs := s.exprs.insert (e, depth) e'? }
      return e'?
  goLevel (u : ℓ) : StateT (ReplaceState ℓ ε) m ℓ := do
    if let some u' ← getf u then
      return u'
    else
      levelMapM goLevel u
  goExpr (e : ε) (depth : Nat) :
      StateT (ReplaceState ℓ ε) m ε := do
    if let some e' ← getg e depth then
      return e'
    else
      exprMapDepthM goLevel goExpr e depth

/--
Replaces subexpressions in `e` using `g`. The function returns `none` if
the children should be visited.
The function is given the current De Bruijn depth.
Caches results by handle, so it's able to preserve sharing.
-/
partial def exprReplaceDepth' [BEq ε] [Hashable ε]
    (g : ε → Nat → m (Option ε))
    (e : ε) (depth : Nat := 0) : m ε :=
  go e depth |>.run' {}
where
  getg (e : ε) (depth : Nat) :
      StateT (Std.HashMap (ε × Nat) (Option ε)) m (Option ε) := do
    if let some e'? := (← get)[(e, depth)]? then
      return e'?
    else
      let e'? ← g e depth
      modify fun s => s.insert (e, depth) e'?
      return e'?
  go (e : ε) (depth : Nat) :
      StateT (Std.HashMap (ε × Nat) (Option ε)) m ε := do
    if let some e' ← getg e depth then
      return e'
    else
      exprMapDepthM' go e depth

end ReplaceExpr

section InstantiateAbstract
variable [BEq ε] [Hashable ε] [MonadGetExpr m ℓ ε] [MonadMkExpr m ℓ ε]

/--
Adds `k` to all loose bvars whose index is at least `i`.
It is up to the caller to make sure that for each loose de Bruijn index `idx`,
`idx + k ≥ 0`.
-/
def exprLiftLooseBVars (e : ε) (i : Nat) (k : Int) : m ε := do
  if k == 0 then
    return e
  else if (← exprLooseBVarRange e) ≤ i then
    return e
  else
    exprReplaceDepth' (e := e) fun e depth => do
      if (← exprLooseBVarRange e) ≤ i + depth then
        -- No loose bvars to lift
        return some e
      else
        match (← getExpr e) with
        | .bvar idx => some <$> mkExprBVar (idx + k).toNat
        | _ => return none -- continue with children expressions

/--
Uses `xs[beginIdx...endIdx]` to instantiate loose bvars in `e`.
Variables are indexed from the end of the subarray,
like `#[, ..., bvar 2, bvar 1, bvar 0]`.
Loose bvars out of range are decremented by `endIdx - beginIdx`.

The expressions in `xs` may have loose bvars, and they will be incremented
by the De Bruijn depth of the occurrence.
-/
def exprInstantiateRev (e : ε) (xs : Array ε)
    (beginIdx := 0) (endIdx := xs.size) : m ε := do
  if beginIdx ≥ endIdx then
    return e
  else if h : endIdx > xs.size then
    panic! "exprInstantiateRev: endIdx out of bounds"
    return e
  else if !(← exprHasLooseBVars e) then
    return e
  else
    exprReplaceDepth' (e := e) fun e depth => do
      if (← exprLooseBVarRange e) ≤ depth then
        -- No loose bvars to substitute
        return some e
      else
        match (← getExpr e) with
        | .bvar idx =>
          if h : idx < depth then
            return some e
          else if h' : idx - depth + beginIdx < endIdx then
            some <$> exprLiftLooseBVars xs[idx - depth + beginIdx] 0 depth
          else
            some <$> mkExprBVar (idx - (endIdx - beginIdx))
        | _ => return none -- continue with children subexpressions

/--
Replaces fvars in `xs[beginIdx...endIdx]` with loose bvars, where the last
element of the subarray gets `bvar 0`.

Note: like in Lean 4, pre-existing loose bvars are *not* modified.
-/
def exprAbstractFVarRev (e : ε) (xs : Array FVarId)
    (beginIdx := 0) (endIdx := xs.size) : m ε := do
  if beginIdx ≥ endIdx then
    return e
  else if h : endIdx > xs.size then
    panic! "exprAbstractFVarRev: endIdx out of bounds"
    return e
  else if !(← exprHasFVar e) then
    return e
  else
    exprReplaceDepth' (e := e) fun e depth => do
      if !(← exprHasFVar e) then
        -- No fvars to abstract
        return some e
      else
        match (← getExpr e) with
        | .fvar fvarId =>
          for h : i in [beginIdx:endIdx] do
            have : i < endIdx := by get_elem_tactic
            have : i < xs.size := by lia
            if xs[i] == fvarId then
              return ← some <$> mkExprBVar (depth + (endIdx - i - 1))
          return some e
        | _ => return none -- continue with children subexpressions

/--
Constructs the application `e xs...` like `mkExprAppN`, but if `e` is a
lambda expression does up to `xs.size` head beta reductions.
-/
partial def mkExprBetaAppN (e : ε) (xs : Array ε) : m ε := do
  go e 0
where
  finalize (e : ε) (endIdx : Nat) : m ε := do
    let e' ← exprInstantiateRev e xs (endIdx := endIdx)
    xs.foldlM (start := endIdx) (init := e') mkExprApp
  go (e : ε) (endIdx : Nat) : m ε := do
    if endIdx < xs.size then
      match (← getExpr e) with
      | .lam _ _ b _ => go b (endIdx + 1)
      | _ => finalize e endIdx
    else
      finalize e endIdx

/--
Like `exprInstantiateRev`, but if substitution creates beta redexes they
are reduced using `mkExprBetaAppN`.
-/
partial def exprInstantiateBetaRev [Inhabited ε] (e : ε) (xs : Array ε)
    (beginIdx := 0) (endIdx := xs.size) : m ε := do
  if beginIdx ≥ endIdx then
    return e
  else if h : endIdx > xs.size then
    panic! "exprInstantiateBetaRev: endIdx out of bounds"
    return e
  else if !(← exprHasLooseBVars e) then
    return e
  else
    go e 0 |>.run' {}
where
  go (e : ε) (depth : Nat) (h : ¬ endIdx > xs.size := by assumption) :
      StateT (Std.HashMap (ε × Nat) ε) m ε := do
    if depth ≤ (← exprLooseBVarRange e) then
      return e
    else if let some e' := (← get)[(e, depth)]? then
      return e'
    else
      let e' ←
        match (← getExpr e) with
        | .bvar idx =>
          if h : idx < depth then
            return e
          else if h' : idx - depth + beginIdx < endIdx then
            exprLiftLooseBVars xs[idx - depth + beginIdx] 0 depth
          else
            mkExprBVar (idx - (endIdx - beginIdx))
        | .app .. =>
          exprWithApp e fun f args => do
            let wasBVar := (← getExpr f) matches .bvar ..
            let f ← go f depth
            let args ← args.mapM (go · depth)
            if wasBVar then
              mkExprBetaAppN f args
            else
              mkExprAppN f args
        | _ => exprMapDepthM' go e depth
      modify fun s => s.insert (e, depth) e'
      return e'


end InstantiateAbstract

section Find
variable [MonadGetExpr m ℓ ε] [BEq ε] [Hashable ε]

partial def exprFind? (e : ε) (p : ε → m Bool) : m (Option ε) := do
  go e |>.run' {}
where
  go (e : ε) : StateT (Std.HashSet ε) m (Option ε) := do
    if (← get).contains e then
      return none
    else
      modify fun s => s.insert e
      if ← p e then
        return some e
      else
        match (← getExpr e) with
        | .bvar _ => return none
        | .fvar _ => return none
        | .mvar _ => return none
        | .sort _ => return none
        | .const _ _ => return none
        | .app fn arg => go fn <||> go arg
        | .lam _ t b _ => go t <||> go b
        | .pi _ t b _ => go t <||> go b
        | .let _ t v b => go t <||> go v <||> go b
        | .lit _ => return none
        | .proj _ _ s => go s

/--
Returns true if there is a loose bvar with index `idx` such that
`beginIdx ≤ i < endIdx`. This is not a constant time operation.
-/
partial def exprHasLooseBVarWithin (e : ε)
    (beginIdx endIdx : Nat) : m Bool := do
  if (← exprLooseBVarRange e) ≤ beginIdx || endIdx ≤ beginIdx then
    return false
  else
    go e 0 |>.run' {}
where
  go (e : ε) (depth : Nat) : StateT (Std.HashSet (ε × Nat)) m Bool := do
    let range ← exprLooseBVarRange e
    if range ≤ beginIdx + depth then
      return false
    else if range ≤ endIdx + depth then
      return true
    else if (← get).contains (e, depth) then
      return false
    else
      modify fun s => s.insert (e, depth)
      match (← getExpr e) with
      | .bvar idx => return beginIdx + depth ≤ idx && idx < endIdx + depth
      | .fvar _ => return false
      | .mvar _ => return false
      | .sort _ => return false
      | .const _ _ => return false
      | .app fn arg => go fn depth <||> go arg depth
      | .lam _ t b _ => go t depth <||> go b (depth + 1)
      | .pi _ t b _ => go t depth <||> go b (depth + 1)
      | .let _ t v b => go t depth <||> go v depth <||> go b (depth + 1)
      | .lit _ => return false
      | .proj _ _ s => go s depth

/--
Returns true if there is a loose bvar with index `i`.
This is not a constant time operation.
-/
partial def exprHasLooseBVarEq (e : ε) (i : Nat) : m Bool := do
  exprHasLooseBVarWithin e i (i + 1)

/--
Creates a bitmap `b` of loose bvars up to but not including index `range`.
This means that `b` has bit `i` set iff `i < range` and it is the index of
a loose bvar.

Using `range = exprLooseBVarRange e` gives the full bitmap.
-/
partial def exprHasLooseBVarBitmap (e : ε) (range : Nat) : m Nat := do
  if !(← exprHasLooseBVars e) then
    return 0
  else
    go e 0 |>.run' {}
where
  go (e : ε) (depth : Nat) : StateT (Std.HashMap (ε × Nat) Nat) m Nat := do
    if (← exprLooseBVarRange e) ≤ depth then
      return 0
    else if let some b := (← get)[(e, depth)]? then
      return b
    else
      let b ←
        match (← getExpr e) with
        | .bvar idx => pure <| if idx < depth + range then (1 <<< (idx - depth)) else 0
        | .fvar _ => pure 0
        | .mvar _ => pure 0
        | .sort _ => pure 0
        | .const _ _ => pure 0
        | .app fn arg => (· ||| ·) <$> go fn depth <*> go arg depth
        | .lam _ t b _ => (· ||| ·) <$> go t depth <*> go b (depth + 1)
        | .pi _ t b _ => (· ||| ·) <$> go t depth <*> go b (depth + 1)
        | .let _ t v b => (· ||| · ||| ·) <$> go t depth <*> go v depth <*> go b (depth + 1)
        | .lit _ => pure 0
        | .proj _ _ s => go s depth
      modify fun s => s.insert (e, depth) b
      return b

end Find

end

end LilLean
