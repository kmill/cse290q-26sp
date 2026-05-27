/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import Lean

public section

namespace LilLean

namespace Parser
/-!
## Syntax definitions for terms
-/

/-- Represents a term of the LilLean language. -/
declare_syntax_cat lilTerm

/-- Represents a tactic of the LilLean language. The "both" behavior prevents
leading tokens in parsers from being reserved as keywords. -/
declare_syntax_cat lilTactic (behavior := both)

namespace LilTerm

/-
Recall these special binding powers:
  lead := 1022 (for "leading" expressions, not part of applications)
  arg  := 1023 (for argument position)
  max  := 1024 (for atoms)
-/

/-- Parentheses. -/
-- Whitespace sensitivity is disabled for the inner term.
syntax:max (name := parens) "(" withoutPosition(lilTerm) ")" : lilTerm

/-- Type ascription. -/
-- Whitespace sensitivity is disabled for the inner terms.
syntax:max (name := ascription) "(" withoutPosition(lilTerm " : " lilTerm) ")" : lilTerm

-- Parse identifiers as `lilTerm`s.
-- Constant. Elaborates to either a local constant (from the local context) or
-- a global constant (from the environment).
attribute [lilTerm_parser] Lean.Parser.Term.ident

-- Parse numeric literals as `lilTerm`s.
-- Numeric literal. Elaborates to an `OfNat.ofNat` expression.
attribute [lilTerm_parser] Lean.Parser.Term.num

-- Parse string literals as `lilTerm`s.
-- String literal.
attribute [lilTerm_parser] Lean.Parser.Term.str

/-- Placeholder. Elaborates to a fresh metavariable. -/
syntax:max (name := placeholder) "_" : lilTerm

/-- Function application. -/
syntax:lead (name := app) lilTerm:max (colGt ws lilTerm:arg)+ : lilTerm

/-- Explicit annotation. For function applications, `@f x y z` means
to ignore explicit/implicit binder annotations in the type of `f`.
For functions, `@fun x y z => ...` means to ignore explicit/implicit binder
annotations in the expected type. -/
syntax:max (name := explicit) "@" lilTerm:max : lilTerm

/-- Explicit binder, with an optional type. -/
syntax explicitBinder := "(" withoutPosition(ident+ (" : " lilTerm)?) ")"
/-- Explicit binder, with a required type. -/
syntax explicitBinderR := "(" withoutPosition(ident+ " : " lilTerm) ")"
/-- Implicit binder, with an optional type. -/
syntax implicitBinder := "{" withoutPosition(ident+ (" : " lilTerm)?) "}"
/-- Implicit binder, with an explicit type. -/
syntax implicitBinderR := "{" withoutPosition(ident+ " : " lilTerm) "}"
/-- Instance implicit binder, with an optional identifier. -/
syntax instImplicitBinder := "[" withoutPosition((ident " : ")? lilTerm) "]"

/-- Binder with optional type annotations, and allowing raw identifiers. -/
syntax binder := ident <|> explicitBinder <|> implicitBinder <|> instImplicitBinder
/-- Binder with required type annotations. -/
syntax binderR := explicitBinderR <|> implicitBinderR <|> instImplicitBinder

/-- Function. -/
syntax:max (name := «fun») "fun " binder+ " => " lilTerm : lilTerm

/-- Arrow (non-dependent function type). Right-associative. -/
syntax:25 (name := arrow) lilTerm:26 " → " lilTerm:25 : lilTerm

/-- Dependent function type. -/
syntax:25 (name := depArrow) binderR " → " lilTerm:25 : lilTerm

/-- Product type (non-dependent). -/
syntax:35 (name := prod) lilTerm:36 " × " lilTerm:35 : lilTerm

/-- Dependent product type. -/
syntax:35 (name := depProd) binderR " × " lilTerm:35 : lilTerm

/-- Anonymous constructor. -/
syntax (name := anonymousCtor) "⟨" lilTerm,*,? "⟩" : lilTerm

/-- `let` definitions. -/
-- optSemicolon matches either `;` or a line break
syntax:lead (name := «let»)
  withPosition("let " ident (" : " lilTerm)? " := " lilTerm)
  optSemicolon(lilTerm) : lilTerm

/-- Type universe. -/
syntax (name := type) "Type" : lilTerm
/-- Prop universe. -/
syntax (name := prop) "Prop" : lilTerm

/-- Apologize to LilLean for not knowing how to fill in this term. -/
syntax:max (name := «sorry») "sorry" : lilTerm

/-- Synthesizes a term using tactics. -/
syntax:lead (name := byTactic) "by " sepBy1IndentSemicolon(lilTactic) : lilTerm

end LilTerm

end Parser

end LilLean
