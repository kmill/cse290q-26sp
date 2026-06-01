/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.LocalContext

/-!
# Metavariable context

This module defines the metavariable context, which manages level and expression
metavariables, and supports abstracting free variables from expressions
containing metavariables whose contexts depend on those variables --- this is
a subtle and rather technical.

Something we do in LilLean is have the metavariable context interface with
the region-based memory allocation in the `LevelContext` and `ExprContext`.
The metavariable context manages back-pointers from older to newer regions
via metavariable assignments, and metavariable instantiation is used to trace
expressions as a garbage collection process before regions are deallocated.
-/

public section

namespace LilLean

end LilLean
