{-# OPTIONS --allow-unsolved-metas #-}
{-
  PaPC AGDA 2024
  Tutorial 4: Lambda calculus and encoding of inductive data types as lambda terms.

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


-- ────────────────────────────
-- ────[ LAMBDA FUNCTIONS ]────
-- ────────────────────────────

-- TUTORIAL: Un-named vs named functions
-- Two different ways to define the following...
id : {A : Set} → A → A
id = {!   !}

something : {A : Set} → ((A → A) → A) → A
something = {!   !}

-- The input to f is a function. You may want to
-- give this input without having to define another
-- function: you can use lambda functions for this.


-- ───────────────────────────────
-- ────[ NATURAL NUMBERS...? ]────
-- ───────────────────────────────

-- EXERCISE**: Play around with and understand the following extended example.

-- A type of function that, in an interesting way, corresponds 
-- to natural numbers!
ℕFun : Set₁
ℕFun = (X : Set) → X → (X → X) → X

-- We can define zero...
zerof : ℕFun
zerof X z s = z

-- And successor...
sucf : ℕFun → ℕFun
sucf n X z s = s (n X z s)

-- And go to and from the usual inductively defined type of 
-- natural numbers as follows:
toℕ : ℕFun → ℕ
toℕ f = f ℕ zero suc

fromℕ : ℕ → ℕFun
fromℕ zero    X z s = z
fromℕ (suc n) X z s = s (fromℕ n X z s)

-- We can define addition for this representation of natural
-- numbers...
_+′_ : ℕFun → ℕFun → ℕFun
(f +′ g) X z s = f X (g X z s) s

-- And multiplication...
_*′_ : ℕFun → ℕFun → ℕFun
(f *′ g) X z s = f X z (λ x → g X x s)

-- We can test that our definitions are correct by doing something
-- like this:
testmult : ℕ → ℕ → ℕ
testmult n m = toℕ (fromℕ n *′ fromℕ m)

-- EXERCISE**: Do the same thing for Bool - i.e. define a type of 
-- (polymorphic) function BoolFun that you can convert to and from Bool.
-- Hint: compare the type ℕFun to the constructors for ℕ:
{-
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
-}
