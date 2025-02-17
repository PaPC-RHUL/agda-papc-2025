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
trans refl q = q

-- EXERCISE: Symmetry of equality
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- TUTORIAL: Every function is congruent wrt equality
cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- EXERCISE: You can use equality to substitute
subst : {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

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

  syntax step-≡-∣ x x≡y      = x ≡⟨⟩ x≡y
  syntax step-≡-⟩ x y≡z x≡y  = x ≡⟨ x≡y ⟩ y≡z

  _∎ : (x : A) → x ≡ x
  x ∎ = refl

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
*-unitl n = +-unitr n

-- EXERCISE: prove that multiplication by 0 on the right is 0.
*-zeror : (n : ℕ) → n * 0 ≡ 0
*-zeror zero    = refl
*-zeror (suc n) = *-zeror n 

-- EXERCISE: prove that one is a right unit for multiplication. Try
-- to use the begin, ≡⟨⟩, ∎ syntax. 
*-unitr : (n : ℕ) → n * 1 ≡ n
*-unitr zero    = refl
*-unitr (suc n) = begin
    suc n * 1
  ≡⟨⟩
    1 + n * 1
  ≡⟨ cong (1 +_) (*-unitr n) ⟩
    suc n
  ∎ 

-- EXERCISE: prove that addition is associative.
+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = begin
    (suc a + b) + c
  ≡⟨⟩
    suc ((a + b) + c)
  ≡⟨ cong suc (+-assoc a b c) ⟩
    suc a + (b + c)
  ∎

-- EXERCISE: prove that addition with a successor on the right behaves
-- as expected. 
-- Hint: pattern match on n
+-sucr : (n m : ℕ) → n + suc m ≡ suc (n + m)
+-sucr zero    m = refl
+-sucr (suc n) m = begin
    suc (n + suc m)
  ≡⟨ cong suc (+-sucr n m) ⟩
    suc (suc (n + m))
  ≡⟨⟩
    suc (suc n + m)
  ∎

-- EXERCISE*: prove that addition is commutative
+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm zero    m = sym (+-unitr m)
+-comm (suc n) m = begin
    suc (n + m)
  ≡⟨ cong suc (+-comm n m) ⟩
    suc (m + n)
  ≡⟨ sym (+-sucr m n) ⟩
    m + suc n
  ∎

-- EXERCISE**: prove that multiplication distributes over 
-- addition
*+-distr : (a b c : ℕ) → a * (b + c) ≡ a * b + a * c 
*+-distr zero    b c = refl
*+-distr (suc a) b c = begin
    b + c + a * (b + c)
  ≡⟨ cong (λ x → b + c + x) (*+-distr a b c) ⟩
    b + c + (a * b + a * c)
  ≡⟨ +-assoc b c (a * b + a * c) ⟩
    b + (c + (a * b + a * c))
  ≡⟨ cong (b +_) (sym (+-assoc c (a * b) (a * c))) ⟩
    b + (c + a * b + a * c)
  ≡⟨ cong (λ x → b + (x + a * c)) (+-comm c (a * b)) ⟩
    b + (a * b + c + a * c)
  ≡⟨ cong (b +_) (+-assoc (a * b) c (a * c)) ⟩
    b + (a * b + (c + a * c))
  ≡⟨ sym (+-assoc b (a * b) (c + a * c)) ⟩
    (b + a * b) + (c + a * c)
  ∎

-- EXERCISE***: prove that multiplication is commutative.
-- This might require you to prove another lemma beforehand,
-- the hard/creative part is to identify this.
-- Hint: look at your proof of commutativity for _+_!
*-suc : (n m : ℕ) → n * suc m ≡ n + n * m
*-suc zero    m = refl
*-suc (suc n) m = begin
    suc (m + n * suc m)
  ≡⟨ cong (suc m +_) (*-suc n m) ⟩
    suc (m + (n + n * m))
  ≡⟨ cong suc (sym (+-assoc m n (n * m))) ⟩
    suc ((m + n) + n * m)
  ≡⟨ cong (λ x → suc (x + n * m)) (+-comm m n) ⟩
    suc ((n + m) + n * m)
  ≡⟨ cong suc ((+-assoc n m (n * m))) ⟩
    suc (n + (m + n * m))
  ∎

*-comm : (n m : ℕ) → n * m ≡ m * n
*-comm zero m = sym (*-zeror m)
*-comm (suc n) m = begin
    m + n * m
  ≡⟨ cong (m +_) (*-comm n m) ⟩ 
    m + m * n
  ≡⟨ sym (*-suc m n) ⟩
    m * suc n
  ∎

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

-- TUTORIAL: successor is monotone wrt less-than-or-equal-to
≤-suc : (n m : ℕ) → n ≤ m → n ≤ suc m
≤-suc zero    m       p        = zero≤
≤-suc (suc n) (suc m) (suc≤ p) = suc≤ (≤-suc n m p)

-- TUTORIAL: Equality "injects" into less-then-or-equal-to
≡-inj-≤ : {n m : ℕ} → n ≡ m → n ≤ m
≡-inj-≤ refl = refl≤ _

-- EXERCISE: prove that less-then-or-equal-to is transitive.
trans≤ : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
trans≤ zero≤    y        = zero≤
trans≤ (suc≤ x) (suc≤ y) = suc≤ (trans≤ x y)

-- EXERCISE*: prove that addition is a congruent wrt less-then-or-equal-to.
-- Hint: you only need to case split on one of a, b, or c!
≤+-pres : (a b c : ℕ) → a ≤ b → a + c ≤ b + c
≤+-pres a b zero    p = subst (λ x → x ≤ b + 0) (sym (+-unitr a)) (subst (λ y → a ≤ y) (sym (+-unitr b)) p)
≤+-pres a b (suc c) p = subst (λ x → x ≤ b + suc c) (sym (+-sucr a c)) (subst (λ y → suc (a + c) ≤ y) (sym (+-sucr b c)) (suc≤ (≤+-pres a b c p)))

-- EXERCISE*: prove that addition is monotone wrt less-than-or-equal-to
≤+-mono : (n m : ℕ) → n ≤ n + m
≤+-mono n zero    = subst (n ≤_) (sym (+-unitr n)) (refl≤ n)
≤+-mono n (suc m) = subst (n ≤_) (sym (+-sucr n m)) (≤-suc n (n + m) (≤+-mono n m))

-- EXERCISE*: prove that multiplication by at least one is monotone wrt
-- less-than-or-equal-to.
-- Hint: can you use the previous exercise directly...?
≤*-suc : (n m : ℕ) → n ≤ suc m * n
≤*-suc n m = ≤+-mono n (m * n)

-- EXERCISE**: prove this!
≤*-lem : (a b c : ℕ) → a ≤ b → a ≤ c → a ≤ b * c
≤*-lem a zero    c       p q = p
≤*-lem a (suc b) zero    p q = subst (a ≤_) (sym (*-zeror b)) q
≤*-lem a (suc b) (suc c) p q = trans≤ q (≤+-mono (suc c) (b * suc c))

open import Data.Product -- imports _×_ and helper functions
open import Data.Sum -- imports _⊎_ and helper functions

-- EXERCISE**: dichotomy of ≤. This exercise might be a stretch, look at 
-- the algebraic data types worksheet if you don't yet understand sum types.
-- Hint: look up the [_,_]′ function in the Data.Sum package
dichotomy : (a b : ℕ) → a ≤ b ⊎ b ≤ a
dichotomy zero    b       = inj₁ zero≤
dichotomy a       zero    = inj₂ zero≤
dichotomy (suc a) (suc b) = [ (λ p → inj₁ (suc≤ p)) , (λ p → inj₂ (suc≤ p)) ]′ (dichotomy a b)

-- EXERCISE**: prove this!
≤+-lem : (a b c : ℕ) → a + b ≤ c → (a ≤ c) × (b ≤ c)
≤+-lem zero    b       c       p = (zero≤ , p)
≤+-lem a       zero    c       p = (subst (_≤ c) (+-unitr a) p , zero≤)
≤+-lem (suc a) (suc b) (suc c) (suc≤ p) = let (p , q) = ≤+-lem a (suc b) c p in suc≤ p , ≤-suc (suc b) c q
