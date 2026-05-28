/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Expr.Context

/-!
# Environment declarations

This module defines the types to represent global constant declarations
in the `Environment`.
-/

public section

namespace LilLean

/--
Hints to guide lazy delta reduction in `isDefEq`.
We compare lex order of the hint/height pair to see which side should be
unfolded first.
-/
inductive ReducibilityHints where
  /-- Unfold eagerly. (Lean 4 calls this `abbrev`.) -/
  | prefer
  /-- Unfold according to definitional height. (Lean 4 has this be the place
  where definitional height is recorded.) -/
  | regular
  /-- Avoid unfolding. (Lean 4 calls this `opaque`, however the kernel can
  unfold all definitions no matter the reducibility hint.) -/
  | avoid
  deriving Inhabited, BEq, Ord

/-- Base structure for declarations. -/
structure ConstantVal where
  name : Name
  levelParams : List Name
  type : ExprId
  /-- Definitional height, representing relative complexity of definitions.
  Used to help guide lazy delta reduction in `isDefEq`.
  In Lean 4, only `DefinitionVal` contains a height. -/
  height : Nat
  deriving Inhabited

structure AxiomVal extends ConstantVal where
  deriving Inhabited

structure DefinitionVal extends ConstantVal where
  value  : ExprId
  hints  : ReducibilityHints
  deriving Inhabited

structure TheoremVal extends ConstantVal where
  value : ExprId
  deriving Inhabited

structure Constructor where
  name : Name
  type : ExprId
  deriving Inhabited

structure InductiveType where
  name : Name
  type : ExprId
  numParams : Nat
  ctors : List Constructor
  deriving Inhabited

/-- Declaration object that can be sent to the kernel. -/
inductive Declaration where
  | axiomDecl (val : AxiomVal)
  | defnDecl (val : DefinitionVal)
  | thmDecl (val : TheoremVal)
  -- | quotDecl
  | inductDecl (val : InductiveType)
  deriving Inhabited

structure InductiveVal extends ConstantVal where
  numParams : Nat
  numIndices : Nat
  /-- The names of the constructors for this inductive datatype. -/
  ctors : List Name
  /-- `true` when recursive (the inductive type appears in the type of at least
  one constructor field). -/
  isRec : Bool
  deriving Inhabited

structure ConstructorVal extends ConstantVal where
  /-- Inductive type name for this constructor. -/
  induct : Name
  /-- Index of this constructor in `InductiveVal.ctors`. -/
  cidx : Nat
  /-- Number of parameters in inductive datatype. -/
  numParams : Nat
  /-- Number of constructor fields (constructor arity minus `numParams`). -/
  numFields : Nat
  deriving Inhabited

structure RecursorRule where
  ctor : Name
  numFields : Nat
  /-- Lambda expression taking the inductive type parameters, the motives,
  and the fields of the constructor. -/
  rhs : ExprId
  deriving Inhabited

structure RecursorVal extends ConstantVal where
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List RecursorRule
  /-- `true` if it supports K-like reduction. This means that the type is an
  inductive predicate with one constructor, and that constructor has no fields.
  The primary example is `Eq`. -/
  k : Bool
  deriving Inhabited

inductive ConstantInfo where
  | axiomInfo  (val : AxiomVal)
  | defnInfo (val : DefinitionVal)
  | thmInfo (val : TheoremVal)
  | inductInfo (val : InductiveVal)
  | ctorInfo (val : ConstructorVal)
  | recInfo (val : RecursorVal)
  deriving Inhabited

namespace ConstantInfo

def toConstantVal : ConstantInfo → ConstantVal
  | .defnInfo     {toConstantVal := d, ..} => d
  | .axiomInfo    {toConstantVal := d, ..} => d
  | .thmInfo      {toConstantVal := d, ..} => d
  | .inductInfo   {toConstantVal := d, ..} => d
  | .ctorInfo     {toConstantVal := d, ..} => d
  | .recInfo      {toConstantVal := d, ..} => d

def name (d : ConstantInfo) : Name :=
  d.toConstantVal.name

def levelParams (d : ConstantInfo) : List Name :=
  d.toConstantVal.levelParams

def type (d : ConstantInfo) : ExprId :=
  d.toConstantVal.type

/--
Returns the value of the declaration, of one exists.
If `allowOpaque` is true then returns the values of theorems.
-/
def value? (info : ConstantInfo) (allowOpaque := false) : Option ExprId :=
  match info with
  | .defnInfo {value, ..}   => some value
  | .thmInfo  {value, ..}   => if allowOpaque then some value else none
  | _                       => none

def hints : ConstantInfo → ReducibilityHints
  | .defnInfo {hints, ..} => hints
  | _                     => .avoid

def height : ConstantInfo → Nat
  | .defnInfo {height, ..} => height
  | _                      => 0

def isDefinition (info : ConstantInfo) : Bool :=
  info matches .defnInfo ..

def isAxiom (info : ConstantInfo) : Bool :=
  info matches .axiomInfo ..

def isTheorem (info : ConstantInfo) : Bool :=
  info matches .thmInfo ..

def isInductive (info : ConstantInfo) : Bool :=
  info matches .inductInfo ..

def isCtor (info : ConstantInfo) : Bool :=
  info matches .ctorInfo ..

def isRecursor (info : ConstantInfo) : Bool :=
  info matches .recInfo ..

end ConstantInfo

end LilLean
