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

section
variable {m : Type → Type} [Monad m]

/--
Applies `f` and `g` to (non-recursively) update handles.
The `g` function gets additional information about the De Bruijn depth.
-/
def Expr.mapM (f : ℓ → m ℓ) (g : ε → Nat → m ε) (e : Expr ℓ ε) (depth : Nat) :
    m (Expr ℓ ε) := do
  match e with
  | .bvar _ => return e
  | .fvar _ => return e
  | .mvar _ => return e
  | .sort u => return .sort (← f u)
  | .const declName us => return .const declName (← us.mapM f)
  | .app fn arg => return .app (← g fn depth) (← g arg depth)
  | .lam n t b i => return .lam n (← g t depth) (← g b (depth + 1)) i
  | .pi n t b i => return .pi n (← g t depth) (← g b (depth + 1)) i
  | .let n t v b => return .let n (← g t depth) (← g v depth) (← g b (depth + 1))
  | .lit _ => return e
  | .proj t i s => return .proj t i (← g s depth)

section
variable [MonadGetExpr m ℓ ε]

def exprHasLevelParam (e : ε) : m Bool := do
  return (← exprHash e) &&& 1 > 0

def exprHasLevelMVar (e : ε) : m Bool := do
  return (← exprHash e) &&& 2 > 0

def exprHasFVar (e : ε) : m Bool := do
  return (← exprHash e) &&& 4 > 0

def exprHasExprMVar (e : ε) : m Bool := do
  return (← exprHash e) &&& 8 > 0

/--
Returns true if the expression has either a level or expression
metavariable.
-/
def exprHasMVar (e : ε) : m Bool := do
  return (← exprHash e) &&& (8 ||| 2) > 0

def exprApproxDepth (e : ε) : m Nat := do
  return (ExprHashData.decode (← exprHash e)).approxDepth.toNat

def exprLooseBVarRange (e : ε) : m Nat := do
  return (ExprHashData.decode (← exprHash e)).looseBVarRange

def exprHasLooseBVars (e : ε) : m Bool := do
  return (← exprLooseBVarRange e) > 0

/--
Returns `true` if `u` and `v` are structurally equal.

If `lax` is true, then ignores binder names and binder info.
(Note: This feature relies on the fact that the hash function ignores these.)
-/
partial def exprEq [BEq ℓ] [BEq ε] (e e' : ε) (lax : Bool := false) :
    m Bool := do
  if e == e' then
    return true
  if (← exprHash e) != (← exprHash e') then
    return false
  match (← getExpr e), (← getExpr e') with
  | .bvar idx, .bvar idx' => return idx == idx'
  | .fvar fvarId, .fvar fvarId' => return fvarId == fvarId'
  | .mvar mvarId, .mvar mvarId' => return mvarId == mvarId'
  | .sort u, .sort u' => levelEq u u'
  | .const c us, .const c' us' =>
    pure (c == c' && us.length == us'.length)
    <&&> (us.zip us').allM fun (u, u') => levelEq u u'
  | .app f a, .app f' a' =>
    exprEq f f' lax <&&> exprEq a a' lax
  | .lam n t b i, .lam n' t' b' i' =>
    pure (lax || (n == n' && i == i'))
    <&&> exprEq t t' lax <&&> exprEq b b' lax
  | .pi n t b i, .pi n' t' b' i' =>
    pure (lax || (n == n' && i == i'))
    <&&> exprEq t t' lax <&&> exprEq b b' lax
  | .let n t v b, .let n' t' v' b' =>
    pure (lax || n == n')
    <&&> exprEq t t' lax <&&> exprEq v v' lax <&&> exprEq b b' lax
  | .lit l, .lit l' => return l == l'
  | .proj t i s, .proj t' i' s' =>
    pure (i == i' && t == t') <&&> exprEq s s' lax
  | _, _ => return false

/--
Returns `true` if `u` and `v` are structurally equal while ignoring binder
names and binder info.
-/
partial def exprEquiv [BEq ℓ] [BEq ε] (e e' : ε) : m Bool :=
  exprEq e e' (lax := true)

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
Applies `f` and `g` to (non-recursively) update handles,
returning the original expression if possible.
-/
def exprMapM (f : ℓ → m ℓ) (g : ε → Nat → m ε) (e : ε) (depth : Nat) : m ε := do
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
Applies `g` to (non-recursively) update handles,
returning the original expression if possible.
-/
def exprMapM' (g : ε → Nat → m ε) (e : ε) (depth : Nat) : m ε := do
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
partial def exprReplace [BEq ℓ] [Hashable ℓ] [BEq ε] [Hashable ε] (e : ε)
    (f : ℓ → m (Option ℓ)) (g : ε → Nat → m (Option ε)) : m ε :=
  goExpr e 0 |>.run' {}
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
      exprMapM goLevel goExpr e depth

/--
Replaces subexpressions in `e` using `g`. The function returns `none` if
the children should be visited.
The function is given the current De Bruijn depth.
Caches results by handle, so it's able to preserve sharing.
-/
partial def exprReplace' [BEq ε] [Hashable ε] (e : ε)
    (g : ε → Nat → m (Option ε)) : m ε :=
  go e 0 |>.run' {}
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
      exprMapM' go e depth

end ReplaceExpr

section InstantiateAbstract
variable [BEq ε] [Hashable ε] [MonadGetExpr m ℓ ε] [MonadMkExpr m ℓ ε]

/-- Adds `k` to all loose bvars whose index is at least `i`. -/
def exprLiftLooseBVars (e : ε) (i : Nat) (k : Int) : m ε := do
  if k == 0 then
    return e
  else if (← exprLooseBVarRange e) ≤ i then
    return e
  else
    exprReplace' e fun e depth => do
      if (← exprLooseBVarRange e) ≤ i + depth then
        -- No loose bvars to lift
        return some e
      else
        match (← getExpr e) with
        | .bvar idx => some <$> mkExprBVar (idx + k : Int).toNat
        | _ => return none -- continue with children expressions

/--
Uses `xs` to instantiate loose bvars in `e`.
Variables are indexed from the end of `xs`,
like `#[, ..., bvar 2, bvar 1, bvar 0]`.
Loose bvars out of range are decremented by `xs.size`.

The expressions in `xs` may have loose bvars, and they will be incremented
by the De Bruijn depth of the occurrence.
-/
def exprInstantiateRev (e : ε) (xs : Array ε) : m ε := do
  if xs.isEmpty then
    return e
  else if !(← exprHasLooseBVars e) then
    return e
  else
    exprReplace' e fun e depth => do
      if !(← exprHasLooseBVars e) then
        -- No loose bvars to substitute
        return some e
      else
        match (← getExpr e) with
        | .bvar idx =>
          if h : idx < depth then
            return some e
          else if h' : idx < xs.size + depth then
            some <$> exprLiftLooseBVars xs[idx - depth] 0 depth
          else
            some <$> mkExprBVar (idx - xs.size)
        | _ => return none -- continue with children subexpressions

/--
Replaces fvars in `xs` with loose bvars, where the last element of `xs`
gets `bvar 0`. Pre-existing loose bvars are *not* modified.
-/
def exprAbstractFVarRev (e : ε) (xs : Array FVarId) (start := 0) (end := 0) : m ε := do
  if xs.isEmpty then
    return e
  else if !(← exprHasFVar e) then
    return e
  else
    exprReplace' e fun e depth => do
      if !(← exprHasFVar e) then
        -- No fvars to abstract
        return some e
      else
        match (← getExpr e) with
        | .fvar fvarId =>
          if let some i := xs.idxOf? fvarId then
            some <$> mkExprBVar (depth + (xs.size - i - 1))
          else
            return some e
        | _ => return none -- continue with children subexpressions

end InstantiateAbstract

end

end LilLean
