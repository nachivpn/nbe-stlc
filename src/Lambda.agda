module Lambda where

open import Type

infixl 5 _,_

data Env : Set where
  [] : Env
  _,_ : (Γ : Env) (a : Ty) → Env

data Var : Env → Ty → Set where
  zero : ∀ {Γ A} → Var (Γ , A) A
  succ : ∀{Γ A B} → Var Γ A → Var (Γ , B) A

data Tm (Γ : Env) : Ty → Set where
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

  -- a restricted fixed point combinator
  fix  : ∀ {A B}
       → Tm Γ ((A ⇒ B) ⇒ (A ⇒ B))
       → Tm Γ A
       → Tm Γ (𝔽 B)
  {-
    A note on `fix`:
    - fix constructs a value of type (𝔽 B), but there is no way 
      to eliminate (F 𝔹) to a 𝔹! This means that a fix application can 
      be passed around, but it's value cannot be read.
    - inspite of this restriction, fix is useful because, for example, 
      we can now write a non-terminating main function using fix. 
      We could also write terminating recursive functions using fix and float
      the value to the top (main function) without inspecting it.
    - this restriction (𝔽 type tag on the result of fix) is necessary for 
      NBE to distinguish a fix point application from a normal application. 
      This is because NBE cannot produce a term of type ⟦ 𝔹 ⟧ without 
      actually evaluating fix---in which case normalization 
      may not terminate!
  -}

