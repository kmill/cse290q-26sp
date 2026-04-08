import Lean
/-!
# Day 3 (Tue, Apr 7, 2026)

Today: lambda calculus, type theory, and the start of the calculus
of constructions.
-/

/-
## Lambda calculus reminder

Notation:
- `fun x => b` for a lambda function
  `x` is the parameter, and `b` is the body
- `a b` is applications
- `a b c`  is  `(a b) c`

-/

#check fun x => x
/-
fun x => x : ?m.1 → ?m.1

The `?m.1` is a *metavariable*, representing some so-far
unknown expression. (Type metavariables in this case.)
-/

#check (fun x => x) true

/-
Conversion rules (a.k.a. definitional equality)

e =?= e'  means that e and e' are *definitionally equal*

Alpha renaming:

fun x => e[x]   =?=   fun y => e[y]

where e[x] means "e with x substituted in"
assuming that this doesn't cause any variable captures.
e.g. this isn't allowed:
  fun x => fun y => x    ≠?≠   fun y => fun y => y   NO!
      ^             |                       ^    |
      ---------------                       ------
      the bindings change, so it's not a valid alpha step
-/
-- This checks that the two expressions are definitionally equal
example : (fun x => x + 1) = (fun y => y + 1) := rfl

-- rfl works
example : (fun x => fun y => x) = (fun x => fun y => x) := rfl
-- rfl doesn't
example : (fun x => fun y => x) = (fun y => fun y => y) := rfl

/-

Beta reduction:
Function application is substitution.

(fun x => e[x]) v   =?=   e[v]
(again, we have to avoid the capturing issue)
-/
#reduce (fun x => [x,x]) (true,false)
-- [(true, false), (true, false)]

/-

Eta reduction:
(fun x => f x)   =?=  f
-/
variable (f : _ → _) in
#check (rfl : (fun x => f x) = f)

/-
How does alpha renaming actually work in Lean?

Answer: Lean doesn't care about the names at all, because
it uses De Bruijn indices.

fun x => fun y => x + y

Pseudo-Lean syntax:

fun => fun => #1 + #0
 ^       ^    |     |
 --------+-----     |
         ------------

fun x => x               fun => #0
fun x y => x             fun => fun => #1
fun x y z => x z (y z)   fun => fun => fun => #2 #0 (#1 #0)

-/

/-
# Types and type contexts

Ingredients:
- What are valid expressions? (Purely syntactic)
- What is a valid context?
- What does it mean for an expression to have a type,
  with respect to a context?

Contexts (Γ):
- Consist of a list of variable names and what type they have
  e.g.
    n : Nat, f : Nat → Nat, β : Type
    ^    ^
    |    type
    variable name

Typing judgment:
  Γ ⊢ e : t

  "in context Γ, e has type t"

e.g.
  n : Nat ⊢ n : Nat


Function types:  (a.k.a "pi types")  ("dependent arrow type")
  (x : t) → t'[x]

  this is the type of functions whose *domain* is t
  and whose *codomain* varies depending on the input x

If t' doesn't actually depend on x, we can write
  t → t'   ("arrow type")

In general, t → t'  is syntax for  (x : t) → t', where x
is not in t'.

-/

#check (n : Nat) → Fin (n + 1)
#check (Fin)
#check fun (n : Nat) => Fin (n + 1)

def myGreatFamily := fun (n : Nat) => Fin (n + 1)
#check (n : Nat) → myGreatFamily n
example : (n : Nat) → myGreatFamily n := Fin.last

/-
Extension to `fun`: it has a type for its parameter.
  fun x : t => e

Typing rules:

       Γ, x : t ⊢ e : t'
-----------------------------------
Γ ⊢ (fun x : t => e) : (x : t) → t'


non-dependent function application:

Γ ⊢ f : t → t'    Γ ⊢ a : t
----------------------------
       Γ ⊢ f a : t'

dependent function application:

Γ ⊢ f : (x : t) → t'    Γ ⊢ a : t
---------------------------------
       Γ ⊢ f a : t'[x := a]

                ~~~~~~~~~~~~
                replace all x's in t' with a

Example of dependent function:
-/
#check Fin.last
-- (n : Nat) → Fin (n + 1)
#check Fin.last 2
-- Fin.last 2 : Fin (2 + 1)

#check Nat.add
-- Nat → Nat → Nat
#check Nat.add 2
-- Nat.add 2 : Nat → Nat

/-!
# Universes

Main basic universe is `Type` (like `*` in System F)

A *type* is any expression `t` such that
  Γ ⊢ t : Type

Rule:
  Γ ⊢ t : Type     Γ, x : t ⊢ t' : Type
  -------------------------------------
      Γ ⊢ ((x : t) → t') : Type


Let's do a derivation:

  Γ = t : Type, t' : t → Type

               -------------------------- [In context]
               Γ, x : t, y : t' x ⊢ x : t
      ------------------------------------------- [Fun]
       Γ, x : t ⊢ (fun y : t' x => x) : t' x → t
  --------------------------------------------------------- [Fun]
  Γ ⊢ (fun x : t => fun y : t' x => x) : (x : t) → t' x → t
-/

/-!
That didn't actually check that the expressions involved were correct.
A full check would need to check that all the rules hold (e.g. the domains of function
types are types)
-/
#check Int
#check Float
#check Int → Float
#check (fun n : Int => Float.ofInt n)

set_option pp.funBinderTypes true
example (t : Type) (t' : t → Type) : (x : t) → t' x → t := by?
  intro x
  intro y
  exact x
