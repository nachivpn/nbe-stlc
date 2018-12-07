
{-# OPTIONS --postfix-projections #-}
module Presheaf where

open import OPE
open import Lambda using (Env)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)

{- 
  Notes: 
  - presheafs allow us to talk about families of Sets indexed by a context Γ
  - presheafs are basically (Tm/Nf/Ne/Var) Γ A, for all Γ "by hiding Γ"
  - for example, the (Var' A →̇ Ne' A) is merely a map from (Var Γ A → Ne Γ A), for all Γ
-}

module Util where

  _⊗_ : ∀{A B C D : Set} → (A → C) → (B → D) → (A × B → C × D)
  f ⊗ g = λ x → f (proj₁ x) , g (proj₂ x)

open Util

-- presheaf over OPE
record 𝒫 : Set₁ where
  field
    -- 𝒪 is the object map of the presheaf over OPE
    𝒪 : Env → Set 
    -- ℱ is the morphism map of the presheaf over OPE
    -- (also called the weakener / weakening)
    ℱ : ∀ {Δ Γ} (τ : Γ ≤ Δ) → (𝒪 Δ → 𝒪 Γ)

open 𝒫

-- family of morphisms used to define a natural transformation
-- this along with naturality defines a natural transformation 𝒫 → 𝒫
-- (also called transformer / transforming)
_→̇_ : (P Q : 𝒫) → Set
_→̇_ P Q = ∀ {Γ} → (P .𝒪 Γ → Q .𝒪 Γ)

-- the unit presheaf
𝟙' : 𝒫
𝟙' = record { 𝒪 = λ Γ → ⊤ ; ℱ = λ τ _ → tt }

-- presheaf product
_×'_ : 𝒫 → 𝒫 → 𝒫
(P ×' Q) .𝒪 Γ = P .𝒪 Γ × Q .𝒪 Γ
(P ×' Q) .ℱ τ = P .ℱ τ ⊗ Q .ℱ τ

-- presheaf exponential
_⇒'_ : 𝒫 → 𝒫 → 𝒫
(P ⇒' Q) .𝒪 Γ      = ∀ {Δ} → Δ ≤ Γ → P .𝒪 Δ → Q .𝒪 Δ
(P ⇒' Q) .ℱ τ f τ' = f (τ ∙ τ')

-- presheaf coproduct
_+'_ : 𝒫 → 𝒫 → 𝒫
(P +' Q) .𝒪 Γ          = P .𝒪 Γ ⊎ Q .𝒪 Γ
(P +' Q) .ℱ τ (inj₁ x) = inj₁ (P .ℱ τ x)
(P +' Q) .ℱ τ (inj₂ y) = inj₂ (Q .ℱ τ y)

module PresheafBCCC where

  evalC : ∀ {A B : 𝒫} → ((A ⇒' B) ×' A) →̇ B
  evalC (f , e) = (f id e)

  curry : ∀ {A B C : 𝒫} → ((A ×' B) →̇ C) → (A →̇ (B ⇒' C))
  curry {A} f = λ a τ b → f (A .ℱ τ a , b)

  -- TODO fst, snd, inl, inr AND laws!
