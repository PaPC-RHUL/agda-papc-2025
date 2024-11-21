{-
  PaPC AGDA 2024
  Tutorial 2: Functions and lambda calculus

  Introduction to named and un-named (anonymous) functions, and 
  how to define functions with lambda syntax. 
  Basics of lambda calculus (encoding of Booleans).

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

-}

variable
  A : Set

-- ────────────────────────────
-- ────[ LAMBDA FUNCTIONS ]────
-- ────────────────────────────

id : A → A
id x = x

id' : A → A
id' = λ x → x

-- TUTORIAL: Un-named vs named functions
pierceish : ((A → A) → A) → A
pierceish f = f id

-- The input to f is a function. You may want to
-- give this input without having to define another
-- function: you can use lambda functions for this.

pierceish' : ((A → A) → A) → A
pierceish' f = f (λ x → x)


