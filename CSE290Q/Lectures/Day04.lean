import Mathlib.Tactic

/-!
# Natural deduction

First-order logic consists of

- propositional logic (with ¬, ∧, ∨, →, ↔, True, and False),
- quantifiers (∀, ∃), and
- propositional and predicate variables

Let's go through the rules of inference for [natural deduction](https://en.wikipedia.org/wiki/Natural_deduction)
and see their equivalents in Lean.

Natural deduction is a proof theory for first-order logic that takes
a "natural"/"constructive" interpretation of each logical connective.
Constructiveness refers to an evidence-based approach to truth (proofs).

---

Notation and basic concepts:

  `p`, `q`, `r`, etc. are propositional (meta)variables

  `h`, `hp`, `hq`, etc. are proof (meta)variables

  `α`, `β`, `γ`, etc. are types

  `h : p`    is pronounced "h is a proof of p"
  `p : Prop` is pronounced "p is a proposition"
  `α : Type` is pronounced "α is a type"
  `x : α`    is pronounced "x has type α"

  A *context* is a list of these `:` pairs, e.g.
    p : Prop, q : Prop, hp : p, hq : q

  `Γ`, etc. are context metavariables

  `Γ ⊢ p : Prop` is the judgment "`p` is a proposition in context `Γ`"

  `Γ ⊢ h : p`    is the judgment "`h` is a proof of `p` in context `Γ`"

  `Γ ⊢ p`        is the judgment "there exists a proof `h` such that `Γ ⊢ h : p`"
                 (we say that `p` is *true* with respect to `Γ` in such a case)

Note that `Γ ⊢ p` is what the Infoview's tactic state shows.

(This `Γ ⊢ p` is that `p` is a syntactic consequence of the hypotheses in `Γ`.
Semantic consequence is different, and often uses `⊨`. We won't talk about this.)

We will use Gentzen-style notation for the rules:

    Γ₁ ⊢ h₁ : p₁   Γ₂ ⊢ h₂ : p₂  ...  Γₙ ⊢ hₙ : pₙ
  ------------------------------------------------- rulename
               Γ ⊢ h : p

This means that, if all the judgements above the line hold,
then so does the judgement below the line.

We might sometimes want to forget the evidence itself and talk
about mere truth:

    Γ₁ ⊢ p₁   Γ₂ ⊢ p₂  ...  Γₙ ⊢ pₙ
  ---------------------------------- rulename
               Γ ⊢ p

Convention:
We will omit `p : Prop`
-/

example (n : Nat) (h : n = n) : n = n := by
  sorry
  /- n : ℕ, h : n = n ⊢ n = n -/

/-!
# Proposition construction
-/

/-!
## Conjunction

  Γ ⊢ p : Prop   Γ ⊢ q : Prop
  --------------------------- ∧
      Γ ⊢ p ∧ q : Prop
-/

variable (p q : Prop) in #check (p ∧ q : Prop)

/-!
## Disjunction

  Γ ⊢ p : Prop   Γ ⊢ q : Prop
  --------------------------- ∨
      Γ ⊢ p ∨ q : Prop
-/

variable (p q : Prop) in #check (p ∨ q : Prop)

/-!
## Implication

  Γ ⊢ p : Prop   Γ ⊢ q : Prop
  --------------------------- →
      Γ ⊢ p → q : Prop
-/

variable (p q : Prop) in #check (p → q : Prop)

/-!
## True


  ----------------- True
   Γ ⊢ True : Prop
-/

#check (True : Prop)

/-!
## False


  ----------------- False
   Γ ⊢ False : Prop
-/

#check (False : Prop)

/-!
## Negation

    Γ ⊢ p : Prop
  ---------------- ¬
   Γ ⊢ ¬ p : Prop

Definition:
  `¬ p`  is  `p → False`
-/

variable (p : Prop) in #check (¬ p : Prop)

/-!
## Biconditional

    Γ ⊢ p : Prop  Γ ⊢ q : Prop
  ----------------------------- ↔
        Γ ⊢ p ↔ q : Prop

-/

variable (p q : Prop) in #check (p ↔ q : Prop)

/-!
# Deduction rules
-/

/-!
## Assumption

   (h : p) in Γ
  ------------- hyp
    Γ ⊢ h : p
-/

variable (p : Prop) (h : p) in #check (h : p)

/-!
## True introduction

 ----------------------- ⊤I
  Γ ⊢ True.intro : True
-/

#check (True.intro : True)

/-!
## Conjunction introduction

     Γ ⊢ hp : p     Γ ⊢ hq : q
  ------------------------------- ∧I
     Γ ⊢ And.intro hp hq : p ∧ q
-/

variable (p q : Prop) (hp : p) (hq : q) in #check (And.intro hp hq : p ∧ q)

/-!
## Disjunction introduction

        Γ ⊢ hp : p
  ------------------------ ∨I₁
    Γ ⊢ Or.inl hp : p ∨ q

        Γ ⊢ hq : q
  ------------------------ ∨I₂
    Γ ⊢ Or.inr hq : p ∨ q
-/

variable (p q : Prop) (hp : p) in #check (Or.inl hp : p ∨ q)
variable (p q : Prop) (hq : q) in #check (Or.inr hq : p ∨ q)
variable (p q : Prop) (hp : p) (hq : q) in #check (Or.inr hq : p ∨ q)

/-!
## Implication introduction
Sometimes the "deduction theorem".

        Γ, hp : p ⊢ hq : q
  ----------------------------------- →I
    Γ ⊢ (fun (hp : p) => hq) : p → q
-/

-- This one is harder to illustrate.

example (p q : Prop) : p → q :=
  fun (hp : p) => (sorry : q)
/-
At the `sorry`, we see that the local context is
  hp : p ⊢ q
which matches what's above the line for →I

We see that `sorry : hq` as well.
So, if we replace `sorry` with a proof of `hq` that (optionally) makes use of `hp`,
we get a proof of `p → q`.
-/

/-!
## Implication elimination (modus ponens)

    Γ ⊢ h : p → q   Γ ⊢ hp : p
  ------------------------------ →E
            Γ ⊢ h hp : q
-/

variable (p q : Prop) (h : p → q) (hp : p) in #check (h hp : q)

-- SKI examples

-- I
example (p : Prop) : p → p :=
  fun (hp : p) => hp

-- K
example (p q : Prop) : p → q → p :=
  fun (hp : p) => fun (_ : q) => hp

set_option pp.funBinderTypes true
example (p q : Prop) : p → q → p := by -- fun (hp : p) (a : q) => hp
  intro hp
  intro
  exact hp

-- S
example (p q r : Prop) : (p → q) → (p → q → r) → (p → r) :=
  fun (hpq : p → q) => fun (hpqr : p → q → r) => fun (hp : p) =>
    hpqr hp (hpq hp)

/-!
## Biconditional introduction

   Γ ⊢ hpq : p → q    Γ ⊢ hqp : q → p
  ------------------------------------ ↔I
     Γ ⊢ Iff.intro hpq hqp : p ↔ q
-/

variable (p q : Prop) (hpq : p → q) (hqp : q → p) in
#check (Iff.intro hpq hqp : p ↔ q)

/-!
## Conjunction elimination

       Γ ⊢ h : p ∧ q
  ---------------------- ∧I₁
     Γ ⊢ And.left h : p

      Γ ⊢ h : p ∧ q
  ---------------------- ∧I₂
     Γ ⊢ And.right h : q
-/

variable (p q : Prop) (h : p ∧ q) in #check (And.left h : p)
variable (p q : Prop) (h : p ∧ q) in #check (And.right h : q)

-- Symmetry of conjunction

theorem and_symm (p q : Prop) : p ∧ q → q ∧ p :=
  fun (h : p ∧ q) => And.intro (And.right h) (And.left h)

#explode and_symm

example (p q : Prop) : p ∧ q → q ∧ p := by?
  intro h
  constructor
  · exact h.2
  · exact h.1

example (p q : Prop) : p ∧ q → q ∧ p :=
  fun (h : p ∧ q) => ⟨h.2, h.1⟩

example (p q : Prop) : p ∧ q → q ∧ p := by?
  intro h
  obtain ⟨hp, hq⟩ := h
  constructor
  · exact hq
  · exact hp

-- Associativity of conjunction

example (p q r : Prop) : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  fun (h : (p ∧ q) ∧ r) =>
    ⟨h.1.1, ⟨h.1.2, h.2⟩⟩

example (p q r : Prop) : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  fun (h : (p ∧ q) ∧ r) =>
    ⟨h.1.1, h.1.2, h.2⟩

-- making use of `match` secretly:
example (p q r : Prop) : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  fun (⟨⟨hp, hq⟩, hr⟩ : (p ∧ q) ∧ r) =>
    ⟨hp, hq, hr⟩

/-!
## Disjunction elimination

    Γ ⊢ h : p ∨ q   Γ ⊢ hp : p → r   Γ ⊢ hq : q → r
  --------------------------------------------------- ∨E
                 Γ ⊢ Or.casesOn h hp hq : r
-/

variable (p q r : Prop) (h : p ∨ q) in
variable (hp : p → r) (hq : q → r) in
#check (Or.casesOn h hp hq : r)


-- Symmetry of disjunction
example (p q : Prop) : p ∨ q → q ∨ p :=
  fun (h : p ∨ q) =>
    Or.casesOn h Or.inr Or.inl

-- Associativity of disjunction

example (p q r : Prop) : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
  fun (h : (p ∨ q) ∨ r) =>
    match h with
    | Or.inl (Or.inl hp) => Or.inl hp
    | Or.inl (Or.inr hq) => Or.inr (Or.inl hq)
    | Or.inr hr          => Or.inr (Or.inr hr)

example (p q r : Prop) : (p ∨ q) ∨ r → p ∨ (q ∨ r) := by tauto

-- Distributivity

/-!
## False elimination (exfalso, "principal of explosion")

        Γ ⊢ h : False
  ------------------------ ⊥E
    Γ ⊢ False.elim h : p
-/

variable (p : Prop) (h : False) in #check (False.elim h : p)


-- Absurdity

example (p : Prop) (h : p) (h' : ¬ p) : 1 = 2 :=
  have := h' h
  False.elim this

example (p : Prop) (h : p) (h' : ¬ p) : 1 = 2 :=
  (h' h).elim

example (p : Prop) (h : p) (h' : ¬ p) : 1 = 2 :=
  absurd h h'

/-!
# Quantifiers
-/

/-!
## Universal introduction

Let `p` denote a predicate with domain `α`.
We encode predicates as functions `p : α → Prop`,
and we write `p x` instead of `p(x)`.

           Γ, x : α ⊢ hp : p x
  ------------------------------------- ∀I
    Γ ⊢ (fun (x : α) => hp) : ∀ x : α, p x

-/

example {α : Type} (p : α → Prop) : ∀ x : α, p x :=
  fun (x : α) => sorry
/-
At `sorry`, we see that the local context is
  x : α  ⊢ p x
which matches what's above the line for →I
-/

/-!
## Existential introduction

Let `p` denote a predicate with domain `α`.

     Γ ⊢ t : α   Γ ⊢ hp : p t
  --------------------------------------- ∃I
    Γ ⊢ Exists.intro t hp : ∃ x : α, p x
-/

variable {α : Type} (p : α → Prop) in
variable (t : α) (hp : p t) in
#check (Exists.intro t hp : ∃ x : α, p x)



/-!
## Universal elimination

    Γ ⊢ h : ∀ x : α, p x   Γ ⊢ t : α
  ------------------------------------ ∀E
            Γ ⊢ h t : p t
-/

variable {α : Type} (p : α → Prop) in
variable (h : ∀ x : α, p x) (t : α) in
#check (h t : p t)

/-!
## Existential elimination

  Γ ⊢ h : ∃ x, p x   Γ, x : α, hp : p x ⊢ hq : q
-------------------------------------------------- ∃E
     Γ ⊢ (let (Exists.intro x hp) := h; hq) : q
-/

example (p : α → Prop) (q : Prop) (h : ∃ x, p x) : q :=
  let ⟨x, hp⟩ := h
  sorry
