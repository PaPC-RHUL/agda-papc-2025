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

-- TUTORIAL: Implement a function "is-tautology₁?" which checks whether
-- a given input function is constantly true. For instance, if f x = x,
-- then "is-tautology₁ f" should evaluate to "false".
-- is-tautology₁ : (Bool → Bool) → Bool
-- is-tautology₁ f = {!!}

-- EXERCISE: Implement a function "is-tautology₂?" which checks whether
-- a given input function of two arguments is constantly true. For
-- instance, if f x y = true, then "is-tautology₂ f" should evaluate to "true".
-- is-tautology₂ : (Bool → Bool → Bool) → Bool
-- is-tautology₂ f = {!!}


-- ───────────────────────────
-- ────[ NATURAL NUMBERS ]────
-- ───────────────────────────

-- The type Nat of natural numbers
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

-- TUTORIAL: Define addition for natural numbers.
_+_ : Nat → Nat → Nat
a + b = ?

-- EXERCISE: Define multiplication for natural numbers.
-- Hint: multiplication is just repeated addition!
_*_ : Nat → Nat → Nat
a * b = ?

-- EXERCISE: Define exponentiation!

-- TUTORIAL: Define a function "eq?" which determines whether its two
-- input numbers are equal. For instance, "eq? zero zero" should evaluate
-- to "true" while "eq? zero (succ zero)" should evaluate to "false".
eq? : Nat → Nat → Bool
eq? a b = {!!}

-- EXERCISE: Define a function that returns true if the
-- first argument is less than or equal to the second, 
-- and false otherwise.
_≤?_ : Nat → Nat → Bool
a ≤? b = ?


-- !!! Beyond this point might need simplifying !!!

-- ─────────────────
-- ────[ TYPES ]────
-- ─────────────────

-- EXERCISE: Describe the following type in simple terms. What are its values?
data Weird : Set where
  foo : Weird → Weird

-- EXERCISE: Define a manifestly empty type called "Empty".
-- Can you define a function Empty → ℕ?
-- Can you define a function in the other direction, so ℕ → Empty?

-- EXERCISE: Write a function "Endo" which takes as input a type X and returns
-- as output the type of functions X → X.
Endo : ?
Endo = ?


-- ─────────────────────────────────────────────
-- ────[ FIRST PROOFS WITH NATURAL NUMBERS ]────
-- ─────────────────────────────────────────────

data IsZero : ℕ → Set where
  case-zero : IsZero zero

data IsNonzero : ℕ → Set where
  case-succ : (n : ℕ) → IsNonzero (succ n)

-- EXERCISE: Prove that the sum of two numbers, both of which are zero, is zero again.
sum-zero : (x y : ℕ) → IsZero x → IsZero y → IsZero (x + y)
sum-zero = ?

-- EXERCISE: State and prove: The sum of two numbers, the first of which is nonzero, is nonzero.
sum-nonzero : ?
sum-nonzero = ?

-- EXERCISE: Prove that the (contradictory) assumption that zero is nonzero implies
-- the (also contradictory) statement that succ zero is zero.
zero-is-not-nonzero : IsNonzero zero → IsZero (succ zero)
zero-is-not-nonzero = ?
