/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Parser.Term

public section

namespace LilLean

namespace Parser
/-!
## Syntax definitions for commands
-/

/-- Represents a command of the LilLean language. -/
declare_syntax_cat lilCommand

namespace LilCommand

syntax (name := «def») "def " ident LilTerm.binder (" : " lilTerm)? " := "
  ppLine
  lilTerm : lilCommand

syntax (name := «theorem») "theorem " ident LilTerm.binder (" : " lilTerm)? " := "
  ppLine
  lilTerm : lilCommand

syntax (name := check) "#check " lilTerm : lilCommand

end LilCommand

end Parser

end LilLean
