module Term where

open import Type

data Var : Ctx → Ty → Set where
  zero : ∀ {Γ A} → Var (Γ , A) A
  succ : ∀{Γ A B} → Var Γ A → Var (Γ , B) A

data Tm (Γ : Ctx) : Ty → Set where
  var  : ∀ {A} → Var Γ A → Tm Γ A

  abs  : ∀ {A B}
    → Tm (Γ , A) B
    -------------------------
    → Tm Γ (A ⇒ B)

  app  : ∀{A B}
      → Tm Γ (A ⇒ B) → Tm Γ A
      -----------------------
      → Tm Γ B

  pair : ∀ {A B}
       → Tm Γ A → Tm Γ B
       -----------------
       → Tm Γ (A * B)

  unit : Tm Γ 𝟙

  fst  : ∀ {A B}
      → Tm Γ (A * B)
      --------------
      → Tm Γ A

  snd  : ∀ {A B}
      → Tm Γ (A * B)
      --------------
      → Tm Γ B

  inl  : ∀ {A B}
      → Tm Γ A
      --------------
      → Tm Γ (A + B)

  inr  : ∀ {A B}
      → Tm Γ B
      --------------
      → Tm Γ (A + B)

  case : ∀ {A B C}
       → Tm Γ (A + B) → Tm (Γ , A) C → Tm (Γ , B) C
       --------------------------------------------
       → Tm Γ C
