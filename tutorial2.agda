{-# OPTIONS --allow-unsolved-metas #-}
{-
  PaPC AGDA 2024
  Tutorial 2: Properties of equality, and more involved 
  proofs about natural numbers!

  ┌─ ADGA MODE SHORTCUTS ─────────────┐    ┌─ BACKSLASH CHARACTERS ─┐
  │ C-c C-l   = load file             │    │ \neg    = ¬            │
  │ C-c C-c   = case split            │    │ \alpha  = α            │
  │ C-c C-SPC = check hole            │    │ \to     = →            │
  │ C-c C-,   = see context and goal  │    │ \cdot   = ·            │
  │ C-c C-.   = see context, goal and │    | \bN     = ℕ            |
  │             type of current term  │    │ \::     = ∷            │
  │ C-c C-d   = display type          │    │ \==     = ≡            │
  │ C-c C-v   = evaluate expression   │    └────────────────────────┘
  └───────────────────────────────────┘    Use C-x C-= to lookup
                                           input method for highlighted 
                                           symbol.
-}

-- We are now going to use the type ℕ (shortcut \bN) of natural numbers 
-- in the Agda standard library, rather than the type Nat that we defined
-- in tutorial one.
-- Note: the successor construct for ℕ is written "suc" (with one "c")!
-- Using Data.Nat lets us specify numbers using decimal notation (6, 13, etc.)
open import Data.Nat hiding (_≤_)
open import Data.Bool hiding (_≤_)

-- ────────────────────
-- ────[ EQUALITY ]────
-- ────────────────────

-- The equality type. ≡ is written as \==. 
infix 4 _≡_
data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

{-
  To do more complicated equational reasoning, we need to develop some helper
  functions that let us manipulate equalities.

  For example, we need to be able to infer that if we have
   - x ≡ y 
   - y ≡ z
  then x ≡ z. This property is called *transitivity* of equality.
-}

-- TUTORIAL: Transitivity of equality
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p q = {!   !}

-- EXERCISE: Symmetry of equality
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym p = {!   !}

-- TUTORIAL: Every function is congruent wrt equality
cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f p = {!   !}

-- EXERCISE: You can use equality to substitute
subst : {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P p px = {!   !}

-- With these, we can now combine equalities together in various ways. 
-- Lets prove some more interesting properties about natural numbers!

-- First we'll introduce some syntax to let us lay out multi-step proofs 
-- in a logical way...
-- You can study the below definitions if you want, but all you really
-- need to know is that they are "syntactic sugar" for trans. 

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 step-≡-∣ step-≡-⟩
  infix  3 _∎

  begin_ : {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  step-≡-∣ : (x : A) {y : A} → x ≡ y → x ≡ y
  step-≡-∣ x x≡y = x≡y

  step-≡-⟩ : (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡-⟩ x y≡z x≡y = trans x≡y y≡z

  syntax step-≡-∣ x x≡y      =  x ≡⟨⟩ x≡y
  syntax step-≡-⟩ x y≡z x≡y  =  x ≡⟨ x≡y ⟩ y≡z

  _∎ : (x : A) → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

-- ────────────────────────────────────
-- ────[ NATURAL NUMBER PROOFS II ]────
-- ────────────────────────────────────

-- Now we are going to build up a library of lemmas: these are smaller
-- proofs that we can use to develop more complicated ones later.

-- TUTORIAL: prove that zero is a right unit for addition
+-unitr : (n : ℕ) → n + 0 ≡ n
+-unitr zero    = refl
+-unitr (suc n) = begin
    suc n + 0
  ≡⟨⟩ -- You can write ≡⟨ ⟩ with \==\< \>
    suc (n + 0)
  ≡⟨ cong suc (+-unitr n) ⟩
    suc n
  ∎ -- \qed

-- TUTORIAL: prove that zero is a right unit for addition (without 
-- the nice-but-perhaps-confusing syntax)
+-unitr' : (n : ℕ) → n + 0 ≡ n
+-unitr' zero    = refl
+-unitr' (suc n) = cong suc (+-unitr n)

-- EXERCISE: prove that one is a left unit for multiplication.
*-unitl : (n : ℕ) → 1 * n ≡ n
*-unitl n = {!   !}

-- EXERCISE: prove that one is a right unit for multiplication. Try
-- to use the begin, ≡⟨⟩, ∎ syntax. 
*-unitr : (n : ℕ) → n * 1 ≡ n
*-unitr n = {!   !}

-- EXERCISE: prove that addition is associative.
+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc = {!   !}

-- EXERCISE: prove that addition with a successor on the right behaves
-- as expected. 
-- Hint: pattern match on n
+-sucr : (n m : ℕ) → n + suc m ≡ suc (n + m)
+-sucr = {!   !}

-- EXERCISE*: prove that addition is commutative
+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm n m = {!   !}

-- EXERCISE**: prove that multiplication distributes over 
-- addition
*+-distr : (a b c : ℕ) → a * (b + c) ≡ a * b + a * c 
*+-distr a b c = {!   !}

-- EXERCISE***: prove that multiplication is commutative.
-- This might require you to prove some separate lemmas 
-- beforehand, the hard part is to identify these.
*-comm : (n m : ℕ) → n * m ≡ m * n
*-comm n m = {!   !}

-- ─────────────────────────────────────
-- ────[ NATURAL NUMBER PROOFS III ]────
-- ─────────────────────────────────────

-- An inductive less-then-or-equal-to type for natural numbers.
-- Elements of n ≤ m can be thought of proofs of the statement 
-- "n is less than or equal to m".
-- ≤ is written with \le 
infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  zero≤ : {n : ℕ} → 0 ≤ n
  suc≤ : {n m : ℕ} → (n≤m : n ≤ m) → suc n ≤ suc m

-- TUTORIAL: Less-than-or-equal-to is reflexive
refl≤ : (n : ℕ) → n ≤ n
refl≤ zero    = zero≤
refl≤ (suc n) = suc≤ (refl≤ n)

-- TUTORIAL: Equality "injects" into less-then-or-equal-to
≡-inj-≤ : {n m : ℕ} → n ≡ m → n ≤ m
≡-inj-≤ refl = refl≤ _

-- EXERCISE: prove that less-then-or-equal-to is transitive.
trans≤ : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
trans≤ = {!   !}

-- EXERCISE*: prove that addition is a congruent wrt less-then-or-equal-to.
≤+-pres : {a b c : ℕ} → a ≤ b → a + c ≤ b + c
≤+-pres = {!   !}

-- EXERCISE*: prove that less-then-or-equal-to "has binary meets".
≤*-pres : {a b c : ℕ} → a ≤ b → a ≤ c → a ≤ b * c
≤*-pres = {!   !}

open import Data.Sum -- imports _⊎_ and helper functions

-- EXERCISE**: dichotomy of ≤. This exercise might be a stretch, look at 
-- the algebraic data types worksheet if you don't yet understand sum types.
dichotomy : {a b : ℕ} → a ≤ b ⊎ b ≤ a
dichotomy = {!   !}
