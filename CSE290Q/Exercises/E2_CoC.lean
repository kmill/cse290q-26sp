import Mathlib.Tactic
/-!
# Calculus of Constructions exercises
-/

namespace CoC

/-!
Since `Prop` is an "impredicative" universe, we can define propositions by
quantifying over all propositions, which includes the proposition we're
defining itself. We can encode each proposition using the type of its
elimination rule.

Note: we need to be careful to use `And`, `Or`, etc., rather than `∧`, `∨`,
etc., to use these encodings rather than the core Lean definitions.
-/

def True := ∀ (p : Prop), p → p
def False := ∀ (p : Prop), p
def And (p q : Prop) := ∀ (r : Prop), (p → q → r) → r
def Or (p q : Prop) := ∀ (r : Prop), (p → r) → (q → r) → r
def Exists {α : Type} (p : α → Prop) := ∀ (r : Prop), ((x : α) → p x → r) → r
def Not (p : Prop) := p → False
def Iff (p q : Prop) := And (p → q) (q → p)

/-!
Assorted exercises. Let's prove properties of the above using only the above
definitions and lambda calculus. Do not use any other definitions or tactics.

Hint: the proofs for the elimination rules should be very easy!
-/

variable {p q r : Prop} {α : Type}

theorem True.trivial : True :=
  sorry

theorem False.elim : False → p :=
  sorry

theorem And.intro (hp : p) (hq : q) : And p q :=
  sorry

theorem And.left (h : And p q) : p :=
  sorry

theorem And.right (h : And p q) : q :=
  sorry

theorem Or.inl (hp : p) : Or p q :=
  sorry

theorem Or.inr (hq : q) : Or p q :=
  sorry

theorem Or.elim (h : Or p q) (hpq : p → r) (hqq : q → r) : r :=
  sorry

theorem Iff.intro (hpq : p → q) (hqp : q → p) : Iff p q :=
  sorry

theorem Iff.mp (h : Iff p q) : p → q :=
  sorry

theorem Iff.mpr (h : Iff p q) : q → p :=
  sorry

theorem Exists.intro {p : α → Prop} (x : α) (hp : p x) : Exists p :=
  sorry

theorem Exists.elim {p : α → Prop}
    (h : Exists p) (hx : ∀ (x : α), p x → r) : r :=
  sorry

/-!
There's no reason to prove theorems about these connectives, since by giving
the correct introduction and elimination rules, we've proved they're the same
as the usual ones. You should be able to take proofs from `E1_TermProofs.lean`
and copy them here to see this (after replacing `∧` with `And`, etc.).
-/

end CoC
