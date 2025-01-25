{-# OPTIONS --allow-unsolved-metas #-}
{-
  PaPC AGDA 2024
  Tutorial 1: Introduction to types and functions

  ┌─ ADGA MODE SHORTCUTS ─────────────┐    ┌─ BACKSLASH CHARACTERS ─┐
  │ C-c C-l   = load file             │    │ \neg    = ¬            │
  │ C-c C-c   = case split            │    │ \alpha  = α            │
  │ C-c C-SPC = check hole            │    │ \to     = →            │
  │ C-c C-,   = see context and goal  │    │ \cdot   = ·            │
  │ C-c C-.   = see context, goal and │    | \bN     = ℕ            |
  │             type of current term  │    │ \::     = ∷            │
  │ C-c C-d   = infer type            │    │ \==     = ≡            │
  │ C-c C-v   = evaluate expression   │    └────────────────────────┘
  └───────────────────────────────────┘    Use C-x C-= to lookup
                                           input method for highlighted 
                                           symbol.
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
zero   + b = b
succ a + b = succ (a + b)

-- EXERCISE: Define multiplication for natural numbers.
-- Hint: multiplication is just repeated addition!
_*_ : Nat → Nat → Nat
zero   * b = zero
succ a * b = b + (a * b)

-- EXERCISE*: Define exponentiation!
_^_ : Nat → Nat → Nat
a ^ zero     = succ zero
a ^ (succ b) = a * (a ^ b)


-- ────────────────────
-- ────[ BOOLEANS ]────
-- ────────────────────

-- TUTORIAL: Define the type Bool of booleans
data Bool : Set where
  true  : Bool
  false : Bool

-- TUTORIAL: Implement boolean "not"
! : Bool → Bool
! true  = false
! false = true

-- TUTORIAL: Implement boolean "and"
_&&_ : Bool → Bool → Bool
true  && b = b
false && b = false 

-- EXERCISE: Implement boolean "or".
-- For example:
--  "false || true" should evaluate to "true".
--  "true  || true" should evaluate to "true".
_||_ : Bool → Bool → Bool
true  || b = true
false || b = b

-- EXERCISE: Implement a function "is-always-true"? which checks whether
-- a given input function (of type Bool → Bool) is constantly true. 
-- For instance, if f x = x, then "is-always-true f" should evaluate 
-- to "false".
is-always-true : (Bool → Bool) → Bool
is-always-true f = f true && f false

-- EXERCISE: Implement a function "is-always-true'" which checks whether
-- a given input function of two arguments is constantly true. For
-- instance, if f x y = true for all x y, then "is-always-true' f" should 
-- evaluate to "true".
is-always-true₂ : (Bool → Bool → Bool) → Bool
is-always-true₂ f = is-always-true (f true) && is-always-true (f false)


-- ────────────────────────────────────────
-- ────[ BOOLEANS AND NATURAL NUMBERS ]────
-- ────────────────────────────────────────

-- EXERCISE: Define a function "eq?" which determines whether its two
-- input numbers are equal. For instance, "eq? zero zero" should evaluate
-- to "true" while "eq? zero (succ zero)" should evaluate to "false".
eq? : Nat → Nat → Bool
eq? zero     zero     = true
eq? zero     (succ _) = false
eq? (succ _) zero     = false
eq? (succ a) (succ b) = eq? a b

-- EXERCISE: Define a function that returns true if the
-- first argument is less than or equal to the second, 
-- and false otherwise.
_≤?_ : Nat → Nat → Bool
zero   ≤? zero   = true
zero   ≤? succ b = true
succ a ≤? zero   = false
succ a ≤? succ b = a ≤? b


-- ─────────────────────────────────────────────
-- ────[ FIRST PROOFS WITH NATURAL NUMBERS ]────
-- ─────────────────────────────────────────────

data IsZero : Nat → Set where
  case-zero : IsZero zero

data IsNonzero : Nat → Set where
  case-succ : (n : Nat) → IsNonzero (succ n)

-- TUTORIAL: Prove that the sum of two numbers, both of which are zero, is zero again.
sum-zero : (x y : Nat) → IsZero x → IsZero y → IsZero (x + y)
sum-zero .zero .zero case-zero case-zero = case-zero

-- TUTORIAL: State and prove: The sum of two numbers, the first of which is nonzero, is nonzero.
sum-nonzero : (x y : Nat) → IsNonzero x → IsZero y → IsNonzero (x + y)
sum-nonzero .(succ n) .zero (case-succ n) case-zero = case-succ (n + zero)

-- EXERCISE: Prove that the (contradictory) assumption that zero is nonzero implies
-- the (also contradictory) statement that succ zero is zero.
zero-is-not-nonzero : IsNonzero zero → IsZero (succ zero)
zero-is-not-nonzero ()

-- EXERCISE*: Prove that multiplication of any number by zero, is zero
zero-absorb : (x y : Nat) → IsZero x → IsZero (y * x)
zero-absorb .zero zero     case-zero = case-zero
zero-absorb .zero (succ y) case-zero = sum-zero zero (y * zero) case-zero (zero-absorb zero y case-zero)

data IsEq : Nat → Nat → Set where
  refl : (n : Nat) → IsEq n n

-- EXERCISE*: Prove that if x = y, then succ x = succ y.
eq-succ : (x y : Nat) → IsEq x y → IsEq (succ x) (succ y)
eq-succ x .x (refl .x) = refl (succ x)

-- EXERCISE*: Prove that multiplication of any number x by 1 (succ zero), is x
one-unit-* : (x : Nat) → IsEq (x * (succ zero)) x
one-unit-* zero     = refl zero
one-unit-* (succ x) = eq-succ (x * (succ zero)) x (one-unit-* x)


-- ─────────────────
-- ────[ TYPES ]────
-- ─────────────────

-- EXERCISE*: Describe the following type in simple terms. What are its values?
data Weird : Set where
  foo : Weird → Weird

-- In order to construct an element of Weird, we can only use the constructor foo.
-- However, to apply foo, we already need to have an element of Weird. For an element
-- of Weird to exist, an element of Weird already needs to exist - this is circular
-- reasoning.
-- The problem here is the lack of a base case - some constructor that creates an 
-- element of type Weird, without already requiring one exists (as an example, consider
-- the constructor zero for Nat).
