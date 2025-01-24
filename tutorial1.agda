{-# OPTIONS --allow-unsolved-metas #-}
{-
  PaPC AGDA 2024
  Tutorial 1: Introduction to types and functions

  ┌─ ADGAPAD SHORTCUTS ───────────────┐    ┌─ BACKSLASH CHARACTERS ─┐
  │ C-c C-l   = load file             │    │ \neg   = ¬             │
  │ C-c C-c   = case split            │    │ \alpha = α             │
  │ C-c C-SPC = check hole            │    │ \to    = →             │
  │ C-c C-,   = see context           │    │ \cdot  = ·             │
  │ C-c C-.   = see context and goal  │    │ \::    = ∷             │
  │ C-c C-d   = display type          │    │ \==    = ≡             │
  │ C-c C-v   = evaluate expression   │    └────────────────────────┘
  │ C-z       = enable Vi keybindings │    Use M-x describe-char to
  │ C-x C-+   = increase font size    │    lookup input method for
  └───────────────────────────────────┘    symbol under cursor.

  Most content is taken from Ingo Blechschmidt's course in 
  Agda at University of Padova 2024.
-}

-- ───────────────────────────
-- ────[ NATURAL NUMBERS ]────
-- ───────────────────────────

-- The type Nat of natural numbers
data Nat : Set where
  zero : Nat
  succ : Nat → Nat

-- TUTORIAL: Define addition for natural numbers.
_+_ : Nat → Nat → Nat
a + b = {!   !}

-- EXERCISE: Define multiplication for natural numbers.
-- Hint: multiplication is just repeated addition!
_*_ : Nat → Nat → Nat
a * b = {!   !}

-- EXERCISE: Define exponentiation!

-- ────────────────────
-- ────[ BOOLEANS ]────
-- ────────────────────

-- TUTORIAL: Define the type Bool of booleans

-- TUTORIAL: Implement boolean "not"

-- TUTORIAL: Implement boolean "and"

-- EXERCISE: Implement boolean "or".
-- "false || true" should evaluate to "true".
-- "true  || true" should evaluate to "true".
-- _||_ : Bool → Bool → Bool
-- a || b = {!!}

-- TUTORIAL: Implement a function "is-always-true"? which checks whether
-- a given input function is constantly true. For instance, if f x = x,
-- then "is-always-true f" should evaluate to "false".
-- is-always-true : (Bool → Bool) → Bool
-- is-always-true f = {!!}

-- EXERCISE: Implement a function "is-always-true'" which checks whether
-- a given input function of two arguments is constantly true. For
-- instance, if f x y = true, then "is-always-true' f" should evaluate to "true".
-- is-always-true₂ : (Bool → Bool → Bool) → Bool
-- is-always-true₂ f = {!!}


-- ────────────────────────────────────────
-- ────[ BOOLEANS AND NATURAL NUMBERS ]────
-- ────────────────────────────────────────

-- TUTORIAL: Define a function "eq?" which determines whether its two
-- input numbers are equal. For instance, "eq? zero zero" should evaluate
-- to "true" while "eq? zero (succ zero)" should evaluate to "false".
-- eq? : Nat → Nat → Bool
-- eq? a b = {!!}

-- EXERCISE: Define a function that returns true if the
-- first argument is less than or equal to the second, 
-- and false otherwise.
-- _≤?_ : Nat → Nat → Bool
-- a ≤? b = ?


-- ─────────────────────────────────────────────
-- ────[ FIRST PROOFS WITH NATURAL NUMBERS ]────
-- ─────────────────────────────────────────────

data IsZero : Nat → Set where
  case-zero : IsZero zero

data IsNonzero : Nat → Set where
  case-succ : (n : Nat) → IsNonzero (succ n)

-- TUTORIAL: Prove that the sum of two numbers, both of which are zero, is zero again.
sum-zero : (x y : Nat) → IsZero x → IsZero y → IsZero (x + y)
sum-zero = {!   !}

-- TUTORIAL: State and prove: The sum of two numbers, the first of which is nonzero, is nonzero.
sum-nonzero : {!   !}
sum-nonzero = {!   !}

-- EXERCISE: Prove that the (contradictory) assumption that zero is nonzero implies
-- the (also contradictory) statement that succ zero is zero.
zero-is-not-nonzero : IsNonzero zero → IsZero (succ zero)
zero-is-not-nonzero = {!   !}

-- TODO: exercises for inductive predicate proofs for properties about multiplication 

data EqNat : Nat → Nat → Set where
  refl : (n : Nat) → EqNat n n


-- ─────────────────
-- ────[ TYPES ]────
-- ─────────────────

-- EXERCISE: Describe the following type in simple terms. What are its values?
data Weird : Set where
  foo : Weird → Weird
