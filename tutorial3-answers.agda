{-
  PaPC AGDA 2024
  Tutorial 3: Algebraic data types

  Introduction to the concept of algebraic data types. Introduction to idea of
  type equivalence (isomorphism).

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
-- in tutorial ontutorial2.agdae.
-- Note: the successor construct for ℕ is written "suc" (with one "c")!
-- Using Data.Nat lets us specify numbers using decimal notation (6, 13, etc.)
open import Data.Nat
open import Data.Bool 

open import Relation.Binary.PropositionalEquality

-- ─────────────────────
-- ────[ SINGLETON ]────
-- ─────────────────────

-- The type with only one element
-- You can write ⊤ with \top
data ⊤ : Set where
  tt : ⊤

-- We can always map into ⊤
unit : {A : Set} → A → ⊤
unit a = tt

-- ──────────────────────
-- ────[ EMPTY TYPE ]────
-- ──────────────────────

-- The type with no elements. Notice there are no
-- constructors!
-- You can write ⊥ with \bot
data ⊥ : Set where

-- We can always map out of ⊥. Notice that we
-- don't actually need to provide a definition,
-- since when we case-split on the input of type ⊥,
-- Agda can tell that it is impossible to construct
-- one.
absurd : {A : Set} → ⊥ → A
absurd ()

-- ────────────────────
-- ────[ PRODUCTS ]────
-- ────────────────────

-- The type of "pairs of an element of A and an element of B"
-- i.e. the type ℕ × Bool is the type whose elements are (ordered) 
-- pairs of natural numbers and Booleans. 
-- You can write × with \times
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ -- This is required to be able to write "fst" instead of "_×_.fst"

-- We call the type A × B the "product of A and B"

example1 : ℕ × Bool
example1 = (1 , false)

example2 : ℕ × Bool → ℕ
example2 (n , b) = n + 1

example3 : ℕ × Bool → ℕ
example3 p = fst p + 1

-- EXERCISE: Product types have interesting connections to function types...
-- define the following (higher-order) functions which convert between the two 
-- types of "functions of two arguments".
curry : {A B C : Set} → (A × B → C) → A → B → C
curry f a b = f (a , b)

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f (a , b) = f a b

-- EXERCISE: Define this higher-order function that "runs two functions in parallel"
pairf : {A B C D : Set} → (A → B) × (C → D) → A × C → B × D
pairf (f , g) (a , c) = (f a , g c)


-- ─────────────────
-- ────[ SUMS ]─────
-- ─────────────────

-- The type where elements are "either" an element of A or an element of B.
-- You can write ⊎ with \uplus
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- We call the type A ⊎ B the "sum of A and B", or the "disjoint union 
-- of A and B"

example4 : ℕ ⊎ Bool
example4 = inr false

example5 : ℕ ⊎ Bool
example5 = inl 5

example6 : ℕ ⊎ Bool → ℕ
example6 (inl x) = x
example6 (inr false) = 0
example6 (inr true)  = 1


-- EXERCISE: Define this higher-order function that "conditionally runs one
-- of two functions"
sumf : {A B C : Set} → (A → B) × (C → B) → A ⊎ C → B
sumf (f , g) (inl a) = f a
sumf (f , g) (inr c) = g c


-- ────────────────────────
-- ────[ ISOMORPHISMS ]────
-- ────────────────────────

-- It is important to have a notion of when two types are "the same".
-- For example, we could define another singleton type with a different name:

data ⊤1 : Set where
  tt1 : ⊤1

-- But should the name of the type really matter? All we should care about are the
-- elements it contains. We can use the notion of an isomorphism to say when we
-- want to consider two types as the same. 
-- For example, an isomorphism between ⊤ and ⊤1 is a pair of functions:

to : ⊤ → ⊤1
to tt = tt1

from : ⊤1 → ⊤
from tt1 = tt

-- such that they are mutually inverse to one another:

from-to : (x : ⊤) → from (to x) ≡ x
from-to tt = refl

to-from : (x : ⊤1) → to (from x) ≡ x
to-from tt1 = refl

-- Two functions with this "mutual inverse" property are enough evidence that
-- we should just consider the types ⊤ and ⊤1 as the same thing.

-- EXERCISE*: Show that A × ⊤ is isomorphic to A
frompair : {A : Set} → A × ⊤ → A
frompair (a , tt) = a

topair : {A : Set} → A → A × ⊤
topair a = (a , tt)

frompair-topair : {A : Set} → (x : A) → frompair (topair x) ≡ x
frompair-topair a = refl

topair-frompair : {A : Set} → (x : A × ⊤) → topair (frompair x) ≡ x
topair-frompair (a , tt) = refl

-- EXERCISE*: Show that A ⊎ ⊥ is isomorphic to A
fromsum : {A : Set} → A ⊎ ⊥ → A
fromsum (inl a) = a

tosum : {A : Set} → A → A ⊎ ⊥
tosum a = inl a

fromsum-tosum : {A : Set} → (x : A) → fromsum (tosum x) ≡ x
fromsum-tosum a = refl

tosum-fromsum : {A : Set} → (x : A ⊎ ⊥) → tosum (fromsum x) ≡ x
tosum-fromsum (inl a) = refl

-- EXERCISE*: Show that A × B is isomorphic to B × A
f1 : {A B : Set} → A × B → B × A
f1 (a , b) = (b , a)

t1 : {A B : Set} → B × A → A × B
t1 (b , a) = (a , b)

f1t1 : {A B : Set} → (x : B × A) → f1 (t1 x) ≡ x
f1t1 (b , a) = refl

t1f1 : {A B : Set} → (x : A × B) → t1 (f1 x) ≡ x
t1f1 (a , b) = refl

-- EXERCISE*: Show that A × (B × C) is isomorphic to (A × B) × C

-- All of these exercises show you that you can really think of × as 
-- being a sort of type multiplication, where the singleton type ⊤ plays 
-- the role of 1.

-- EXERCISE****: Show that ℕ ⊎ ℕ is isomorphic to ℕ
-- This is *very* difficult and may require some equality combinators and 
-- extra functions. Think of it as a project.

open import Data.Nat.Properties

f3 : ℕ ⊎ ℕ → ℕ
f3 (inl n) = 2 * n
f3 (inr n) = 2 * n + 1

iseven : ℕ → Bool
iseven zero = true
iseven (suc zero) = false
iseven (2+ n) = iseven n

t3 : ℕ → ℕ ⊎ ℕ
t3 n = if iseven n 
        then inl (n / 2) 
        else inr ((n / 2) ∸ 1)

f3t3 : (n : ℕ) → f3 (t3 n) ≡ n
f3t3 zero       = refl
f3t3 (suc zero) = refl
f3t3 (2+ n) with iseven n
... | false = {!   !}
... | true  = {!   !}
