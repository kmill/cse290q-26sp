import Batteries
import Mathlib.Logic.Equiv.Defs

/-!
# Inductive types


-/

          -- type former
          -- |      resulting universe
          -- v      v
inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

-- Every constructor type must end in the inductive type itself

                 -- inductive type parameter
                 -- v
                 ----------
inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α

-- Inductive type parameters are the parameters to the type former that
-- are fixed over all constructors.
-- They have to come first, and the arguments to the constructors have
-- to come in the same order.

-- We can see the inductive type parameters in the constructor types

#check @MyList.nil
-- @MyList.nil : {α : Type} → MyList α
--               ~~~~~~~~~~
--               induct. param.
#check @MyList.cons
-- @MyList.cons : {α : Type} → α → MyList α → MyList α
--               ~~~~~~~~~~    ~~~~~~~~~~~~
--               induct. param.   two fields

/-
Morally, `MyList α` is a different type for each choice of `α`.
It's a *parameterized family* of types.
-/

inductive MyList'.{u} (α : Type u) : Type u where
  | nil : MyList' α
  | cons : α → MyList' α → MyList' α
-- Rule: the universe levels for the fields must all fit inside
-- the inductive type's resulting universe level
-- Why? Fields represent data, and it's stored.
-- Inductive type parameters don't play a role in this constraint.

#check @MyList'
universe u_1 in
#check Type u_1 → Type u_1

-- set_option inductive.autoPromoteIndices false
inductive MyList''.{u} : Type u → Type u where
  | nil {α : Type u} : MyList'' α
  | cons : {α : Type u} → α → MyList'' α → MyList'' α
  -- | natCons : (n : Nat) → MyList'' (ULift Nat) → MyList'' (ULift Nat)

#check PLift
#check ULift

/-
Example of bad parameter:
inductive MyVector.{u} (α : Type u) (n : Nat) : Type u where
  | nil  : MyVector α n
  | cons :  α → MyVector α (n + 1) → MyVector α n
-/

inductive MyVector.{u} (α : Type u) : Nat → Type u where
  | nil : MyVector α 0
  | cons : {n : Nat} → α → MyVector α n → MyVector α (n + 1)

#print MyVector
-- one parameter, one index

#check @MyVector
-- MyVector : Type u_1 → Nat → Type u_1
--            ~~~~~~~~   ~~~
--            |           index
--            inductive type parameter

/-
The `Nat` parameter to the type former is an *index* because it isn't
uniform across all occurrences of `MyVector` in the constructors.
-/

structure MyVector' (α : Type u) (n : Nat) : Type u where
  lst : List α
  length_eq : lst.length = n

def MyVector.toList {α} {n} : MyVector α n → List α
  | .nil => []
  | .cons x xs => x :: xs.toList

def List.toMyVector {α} : (xs : List α) → MyVector α xs.length
  | [] => .nil
  | x :: xs => .cons x xs.toMyVector

def MyVector.cast {α} {n n' : Nat} (h : n = n') (v : MyVector α n) :
    MyVector α n' :=
  h ▸ v

example (α : Type u) (n : Nat) : MyVector α n ≃ MyVector' α n where
  toFun v := { lst := v.toList, length_eq := sorry }
  invFun xs := xs.lst.toMyVector.cast xs.length_eq
  left_inv := by
    intro v
    sorry
  right_inv := by
    sorry

/-
inductive MyEq {α : Type u} : α → α → Prop where
  | rfl (x : α) : MyEq x x
-/
inductive MyEq {α : Type u} (x : α) : α → Prop where
  | rfl : MyEq x x

#check @MyEq
-- @MyEq : {α : Type u_1} → α → α → Prop
--         ~~~~~~~~~~~~~~~~~~  ~~~
--          inductive type     index
--          parameters
#check @MyEq.rfl
-- @MyEq.rfl : {α : Type u_1} → (x : α) → MyEq x x
--             ~~~~~~~~~~~~~~~~~~~~~~~~
--               two parameters           (and zero fields)

/-
The K rule applies to inductive types that don't contain any data,
specifically, there must be just one constructor, and that constructor
has no fields.
(This only applies to `Prop` inductive types)

What this means is that given `h : MyEq x x`, we can assume that `h`
is definitionally equal to `rfl x`.
(Syntactic subsingleton elimination).

We can also have so-called *large elimination*
-/

example (a b : Nat) : MyEq (a + b) (b + a) := by
  induction b with
  | zero => simp; exact MyEq.rfl
  | succ b' ih =>
    rw [Nat.succ_add, Nat.add_succ]
    refine MyEq.recOn ih ?_
    exact MyEq.rfl

#check @MyList.rec
/-
@MyList.rec : {α : Type} →     -- inductive type parameters
  {motive : MyList α → Sort u_1} →   -- motive(s)
  -- minor premise for nil :
  (nil : motive MyList.nil) →
  -- minor premise for cons:
  (cons : (a : α) → (a_1 : MyList α) → motive a_1 →  -- <- arguments corresponding
    motive (MyList.cons a a_1)) →                    --    to fields
  -- indices (if present)
  (t : MyList α) → -- major premise
  motive t  -- result
-/

/-
-- simplified to be a fold:
@MyList.fold : {α : Type} →     -- inductive type parameters
  {motive : Sort u_1} →   -- motive(s)
  -- minor premise for nil :
  (nil : motive) →
  -- minor premise for cons:
  (cons : (a : α) → motive →  -- <- arguments corresponding
    motive) →                    --    to fields
  -- indices (if present)
  (t : MyList α) → -- major premise
  motive  -- result
-/

#check @MyNat.rec
/-
@MyNat.rec : -- 0 parameters
  -- motive:
  {motive : MyNat → Sort u_1} →
  -- minor premise for `zero`:
  (zero : motive MyNat.zero) →
  -- minor premise for `succ`:
  (succ : (a : MyNat) → motive a → motive a.succ) →
  (t : MyNat) → -- major premise
  motive t
-/

#check @MyVector.rec
/-
@MyVector.rec : {α : Type u_2} → -- 1 parameter
  -- 1 motive:
  {motive : (a : Nat) → MyVector α a → Sort u_1} →
  -- minor premise for `nil`:
  (nil : motive 0 MyVector.nil) →
  -- minor premise for `cons`:
  (cons : {n : Nat} → (a : α) → (a_1 : MyVector α n) → motive n a_1 →
    motive (n + 1) (MyVector.cons a a_1)) →
  -- 1 index:
  {a : Nat} →
  -- major premise:
  (t : MyVector α a) →
  -- resulting type:
  motive a t
-/
-- Nothing special about indices in minor premises; indices are
-- computed from fields after all.

set_option pp.proofs true
#check @MyEq.rec
/-
@MyEq.rec : {α : Type u_2} → {x : α} →  -- two parameters
  -- motive (with large elimination)
  {motive : (a : α) → MyEq x a → Sort u_1} →
  -- minor premise
  (rfl : motive x MyEq.rfl) →
  -- 1 index
  {a : α} →
  -- major premise
  (t : MyEq x a) →
  -- resulting type:
  motive a t
-/

#check @Or.rec
/-
@Or.rec : {a b : Prop} → -- two parameters
  -- motive (with *small* elimination)
  {motive : a ∨ b → Prop} →
  -- two minor premises
  (inl : ∀ (h : a), motive (Or.inl h)) →
  (inr : ∀ (h : b), motive (Or.inr h)) →
  -- major premise
  (t : a ∨ b) →
  -- resulting type
  motive t
-/

#print MyNat.rec
/-
@MyNat.rec motive zero succ MyNat.zero
  =*>  zero
       : motive MyNat.zero
@MyNat.rec motive zero succ (MyNat.succ n)
  =*>  succ n (@MyNat.rec motive zero succ n)
       : motive (MyNat.succ n)
-/

#print Or.rec
/-
@Or.rec motive inl inr (Or.inl h)
  =*>  inl h
@Or.rec motive inl inr (Or.inr h)
  =*>  inr h
-/

axiom Or.badRec {a b : Prop}
  -- motive (with *large* elimination)
  {motive : a ∨ b → Sort u}
  -- two minor premises
  (inl : ∀ (h : a), motive (Or.inl h))
  (inr : ∀ (h : b), motive (Or.inr h))
  -- major premise
  (t : a ∨ b) :
  -- resulting type
  motive t

axiom Or.badRec_inl {a b : Prop}
  {motive : a ∨ b → Sort u}
  (inl : ∀ (h : a), motive (Or.inl h))
  (inr : ∀ (h : b), motive (Or.inr h))
  (h : a) :
  @Or.badRec a b motive inl inr (Or.inl h) = inl h

axiom Or.badRec_inr {a b : Prop}
  {motive : a ∨ b → Sort u}
  (inl : ∀ (h : a), motive (Or.inl h))
  (inr : ∀ (h : b), motive (Or.inr h))
  (h : b) :
  @Or.badRec a b motive inl inr (Or.inr h) = inr h

noncomputable
def Or.wasLeft {a b : Prop} (h : a ∨ b) : Bool :=
  @Or.badRec a b
    (motive := fun _ => Bool)
    (inl := fun _ => true)
    (inr := fun _ => false)
    h

example : False :=
  have : true = false :=
    let pf1 : True ∨ True := Or.inl trivial
    let pf2 : True ∨ True := Or.inr trivial
    have h1 : Or.wasLeft pf1 = Or.wasLeft pf2 := rfl
    have h2 : Or.wasLeft pf1 = true :=
      Or.badRec_inl _ _ trivial
    have h3 : Or.wasLeft pf2 = false :=
      Or.badRec_inr _ _ trivial
    by rw [← h2, h1, h3]
  Bool.noConfusion this

-- That's why `Or` can't have large elimination,
-- we can make decisions about which proof it was
-- but we have definitional proof irrelevance


-----

inductive MyEmpty where

#check @MyEmpty.rec

/-
inductive Bad : Type where
  | mk : (Bad → Empty) → Bad
/-
(kernel) arg #1 of 'Bad.mk' has a non positive
occurrence of the datatypes being declared
-/
-/

axiom Bad : Type
axiom Bad.mk : (Bad → Empty) → Bad
axiom Bad.cases {motive : Sort u}
    (mk : (f : Bad → Empty) → motive)
    (t : Bad) : motive
axiom Bad.cases_mk {motive : Sort u}
    (mk : (f : Bad → Empty) → motive)
    (f : Bad → Empty) :
    @Bad.cases motive mk (Bad.mk f) = mk f

example : False :=
  have f : Bad → Empty :=
    Bad.cases (fun f => f (Bad.mk f))
  have b : Bad := Bad.mk f
  have : Empty := f b
  this.elim
