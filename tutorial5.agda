{-# OPTIONS --allow-unsolved-metas #-}
{-
  PaPC AGDA 2024
  Tutorial 5: Propositions as types

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

variable
  A B C : Set

-- ──────────────────────────────
-- ────[ PROPOITIONAL LOGIC ]────
-- ──────────────────────────────

-- The idea here is that you can think of logical propositions as types
-- and elements of those types as proofs of those logical propositions.

-- TUTORIAL: Define "true" and "false" as types

-- If A implies false, then A is "not true"
-- TUTORIAL: Define "not"

-- A proof of A and B is a pair: a proof of A *and* a proof of B
-- TUTORIAL: Define "and" (product types)
data _∧_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A ∧ B

-- A proof of A or B is *either* a proof of A *or* a proof of B
-- TUTORIAL: Define "or" (sum types)
data _∨_ (A : Set) (B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

-- TUTORIAL: Show that A ∧ B implies A ∨ B

-- TUTORIAL: Show that (A → B) ∧ A implies B

-- EXERCISE: Show that (A → B) ∧ (B → C) implies A → C
-- ex1 : (A → B) → (B → C) → (A → C)
-- ex1 = ?

-- EXERCISE: Show that (A → B) ∨ (A → C) implies A → (B ∨ C)
-- ex2 : (A → B) ∨ (A → C) → (A → (B ∨ C))
-- ex2 = ?

-- EXERCISE: Show that ¬ A implies ¬ (A ∧ B)
-- ex3 : (A → ⊥) → ((A ∧ B) → ⊥)
-- ex3 = ?


-- ─────────────────────────────
-- ────[ FIRST ORDER LOGIC ]────
-- ─────────────────────────────

