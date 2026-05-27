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
declare_syntax_cat lilLevel

namespace LilLevel

/-- Parentheses. -/
syntax:max (name := parens) "(" withoutPosition(lilLevel) ")" : lilLevel

-- Parse identifiers as `lilLevel`s.
-- Universe parameter.
attribute [lilLevel_parser] Lean.Parser.Term.ident

-- Parse numerals as `lilLevel`s.
-- Concrete Universe level.
attribute [lilLevel_parser] Lean.Parser.Term.num

/-- Placeholder. Elaborates to a fresh metavariable. -/
syntax:max (name := placeholder) "_" : lilLevel

syntax:65 (name := addOffset) lilLevel:65 " + " num : lilLevel

-- hack to get (includeIdent := true), which isn't exposed to `syntax`
open Lean.Parser (nonReservedSymbol)
meta def maxSymbol := nonReservedSymbol "max" (includeIdent := true)
meta def iposSymbol := nonReservedSymbol "ipos" (includeIdent := true)

syntax (name := max) maxSymbol (ppSpace lilLevel:max)+ : lilLevel
syntax (name := ipos) iposSymbol (ppSpace lilLevel:max)+ : lilLevel

open Lean PrettyPrinter Parenthesizer
@[category_parenthesizer lilLevel]
meta def lilLevel.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `lilLevel true wrapParens prec $
    parenthesizeCategoryCore `lilLevel prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run `(lilLevel| ($(⟨stx⟩)))

end LilLevel

end Parser

end LilLean
