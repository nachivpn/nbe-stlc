
{-# OPTIONS --postfix-projections #-}
module Presheaf where

open import Thinning
open import Type using (Ctx)
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
    -- F is the object map of the presheaf over OPE
    F : Ctx → Set
    -- fmap is the morphism map of the presheaf over OPE
    -- (also called the weakener / weakening)
    fmap : ∀ {Δ Γ} (τ : Γ ≤ Δ) → (F Δ → F Γ)

open 𝒫

-- family of morphisms used to define a natural transformation
-- this along with naturality defines a natural transformation 𝒫 → 𝒫
-- (also called transformer / transforming)
_→̇_ : (P Q : 𝒫) → Set
_→̇_ P Q = ∀ {Γ} → (P .F Γ → Q .F Γ)

-- the unit presheaf
𝟙' : 𝒫
𝟙' .F _      = ⊤
𝟙' .fmap _ _ = tt

-- presheaf product
_×'_ : 𝒫 → 𝒫 → 𝒫
(P ×' Q) .F Γ = P .F Γ × Q .F Γ
(P ×' Q) .fmap e = P .fmap e ⊗ Q .fmap e

-- presheaf exponential
_⇒'_ : 𝒫 → 𝒫 → 𝒫
(P ⇒' Q) .F Γ      = ∀ {Δ} → Δ ≤ Γ → P .F Δ → Q .F Δ
(P ⇒' Q) .fmap e f e' = f (e ∙ e')

-- presheaf coproduct
_+'_ : 𝒫 → 𝒫 → 𝒫
(P +' Q) .F Γ          = P .F Γ ⊎ Q .F Γ
(P +' Q) .fmap e (inj₁ x) = inj₁ (P .fmap e x)
(P +' Q) .fmap e (inj₂ y) = inj₂ (Q .fmap e y)

module PresheafBCCC where

  evalC : ∀ {A B : 𝒫} → ((A ⇒' B) ×' A) →̇ B
  evalC (f , e) = (f id e)

  curry : ∀ {A B C : 𝒫} → ((A ×' B) →̇ C) → (A →̇ (B ⇒' C))
  curry {A} f = λ a e b → f (A .fmap e a , b)

  -- TODO fst, snd, inl, inr AND laws!
