/-!
## Impredicativity

Predicativity: definitions are not allowed to have
quantifiers that range over some domain that includes
the thing being defined.

Impredicativity: you allow it.

Lean's Prop universe of propositions is impredicative.
-/

#check ∀ (n : Nat), n = n
#check ∀ (n : Nat), Prop
#check ∀ (n : Nat), Type

#check Nat → Nat

#check Type
#check Type 0
#check Type 1
#check Type 2
universe u in
#check Type u

variable (α : Type u) (β : Type v) in
#check α → β
-- α → β : Type (max u v)

example : Type 40 := PUnit

structure SM (Λ : Type) where
  σ : Type
  τ : σ → Λ → σ
  accept : σ → Bool
  init : σ

#check SM
-- It's in Type 1, so there's a universe bump

#check Fin 2
#check (0 : Fin 2)
#check (1 : Fin 2)

def SM.parity : SM (Fin 2) where
  σ := Bool
  τ s x := --s != (x == 1)
    if x == 1 then
      !s
    else
      s
  init := true
  accept s := s

def SM.run {Λ : Type} (m : SM Λ)
    (xs : List Λ) (s : m.σ := m.init) : Bool :=
  match xs with
  | [] => m.accept s
  | x::xs' =>
    let s' := m.τ s x
    m.run xs' s'

def SM.run' {Λ : Type} (m : SM Λ) (xs : List Λ) : Bool :=
  match xs with
  | [] => m.accept m.init
  | x::xs' =>
    let m' := { m with init := m.τ m.init x }
    m'.run' xs'

#eval SM.parity.run []
#eval SM.parity.run [0,1]
#eval SM.parity.run [0,1,0]
#eval SM.parity.run [0,1,0,1]

#eval List.sum ([0,1,0,1] : List (Fin 2))

theorem aux (xs : List (Fin 2)) (s : Bool) :
    SM.parity.run xs s
      = (List.sum xs = if s then 0 else 1) := by
  induction xs generalizing s with
  | nil =>
    cases s <;> simp [SM.run, SM.parity]
  | cons x xs ih =>
    simp [SM.run, ih]
    simp [SM.parity]
    split <;> split <;> subst_vars <;> grind

example (xs : List (Fin 2)) :
    SM.parity.run xs = (List.sum xs = 0) := by
  rw [aux]
  simp [SM.parity]


structure SM'.{u} (Λ : Type) where
  σ : Type u
  τ : σ → Λ → σ
  accept : σ → Bool
  init : σ

def SM'.canonical (m : SM'.{u} Λ) : SM'.{u+1} Λ where
  σ := SM'.{u} Λ
  τ m x := { m with init := m.τ m.init x }
  accept m := m.accept m.init
  init := m

def Language (Λ : Type) := List Λ → Bool

/--
`lang.deriv x` is the set of all strings `xs` such that `x :: xs` is in `lang`.

e.g.
`lang = {"abc", "apple", "banana"}`

`lang.deriv "a" = {"bc, "pple"}`
`lang.deriv "b" = {"anana"}`
`lang.deriv "c" = {}`
`(lang.deriv "a").deriv "b" = {"c"}`
`((lang.deriv "a").deriv "b").deriv "c" = {""}`
-/
def Language.deriv {Λ : Type} (x : Λ) (lang : Language Λ) : Language Λ :=
  fun xs => lang (x :: xs)

def Language.accepts {Λ : Type} (lang : Language Λ) (xs : List Λ) : Bool :=
  match xs with
  | [] => lang []
  | x::xs' => (lang.deriv x).accepts xs'

example {Λ : Type} (lang : Language Λ) (xs : List Λ) :
    lang.accepts xs ↔ lang xs := by
  sorry

def SM.toLanguage {Λ : Type} (m : SM Λ) : Language Λ :=
  m.run

def Language.toSM {Λ : Type} (lang : Language Λ) : SM Λ where
  σ := Language Λ
  init := lang
  accept lang' := lang' []
  τ lang' := lang'.deriv

def SM.canonical {Λ : Type} (sm : SM Λ) : SM Λ :=
  sm.toLanguage.toSM


--

#check Sort 0
#check Sort 1
#check Sort 2
-- In general:
-- Sort 0     = Prop
-- Sort (u+1) = Type u

universe u v in
variable (α : Sort u) (β : Sort v) in
#check α → β
-- α → β : Sort (imax u v)
-- "impredicative max"
-- imax u 0  =  0
-- imax u (v+1) = max u (v+1)

universe u v in
variable (α : Sort u) (β : Prop) in
#check α → β
-- ∀ (a : α), β : Prop
universe u v in
variable (α : Sort u) (β : Type v) in
#check α → β
-- α → β : Sort (max u (v + 1))

#check fun n : Nat => ∀ (p : Nat → Prop), p n
-- : Nat → Prop
-- So, this ∀ ranges over the function itself.

#check Nat.rec
/-
Nat.rec.{u} {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) :
  motive t
-/



/-
# Office hours afterwards

Codata

coinductive Language (Λ : Type) where
  | mk (hasNil : Bool) (deriv : Λ → Language Λ)

coinductive Process (Λ : Type) where
  | mk (canStop : Bool) (step : Λ → Process Λ)
-/

inductive ProcessMk (Λ : Type) (σ : Type u) where
  | mk (canStop : Bool) (step : Λ → σ)

variable (Λ : Type) in
#check ProcessMk Λ (ProcessMk Λ (ProcessMk Λ (ProcessMk Λ (ProcessMk Λ (
  ProcessMk Λ (ProcessMk Λ (ProcessMk Λ (ProcessMk Λ Unit))))))))

-- def Language.corec.{u} {Λ : Type} (σ : Type u)
--     (f : σ → ProcessMk Λ σ) : σ → Language Λ :=
--   sorry

-- def Language.corec.{u} {Λ : Type} (σ : Type u)
--     (f : σ → Bool × (Λ → σ)) : σ → Language Λ :=
--   sorry


def SM'.run {Λ : Type} (m : SM' Λ)
    (xs : List Λ) (s : m.σ := m.init) : Bool :=
  match xs with
  | [] => m.accept s
  | x::xs' =>
    let s' := m.τ s x
    m.run xs' s'

theorem SM'.run_eq {Λ : Type} (m : SM' Λ)
    (xs : List Λ) {s : m.σ} (s' : m.σ) :
    {m with init := s'}.run xs s = m.run xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp [SM'.run]
    rw [ih]

theorem SM'.mk_run_eq {Λ : Type}
    (σ : Type u) (τ : σ → Λ → σ) (init init' : σ)
    (accept : σ → Bool) (s : σ)
    (xs : List Λ) :
    {σ, τ, accept, init : SM' Λ}.run xs s =
      {σ, τ, accept, init := init' : SM' Λ}.run xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp [run, ih]

universe u

def Language.corec {Λ : Type} {σ : Type u}
    (accept : σ → Bool)
    (τ : σ → Λ → σ) :
    σ → Language Λ :=
  fun init => ({ σ, τ, init, accept : SM' Λ }).run

def Language.mk {Λ : Type}
    (hasNil : Bool) (step : Λ → Language Λ) :
    Language Λ :=
  fun xs =>
    match xs with
    | [] => hasNil
    | x::xs' => step x xs'


/--
Computation rule for corec matching
```
match Language.corec accept τ init with
| Language.mk b t => f b t

=>

f (accept init) (fun x => Language.corec accept τ (τ init x))
```
-/
theorem Language.corec_step  {Λ : Type} (σ : Type u)
    (accept : σ → Bool)
    (τ : σ → Λ → σ) (init : σ) :
    Language.corec accept τ init =
      Language.mk (accept init)
        (fun x => Language.corec accept τ (τ init x)) := by
  funext xs
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp [corec, SM'.run, mk]
    exact SM'.mk_run_eq ..
