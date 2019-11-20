module OPE where

open import Lambda using (Env ; Var ; Tm)
open Env
open Var
open Tm
open import Type

infix 4 _≤_

-- Order Preserving Embedding (OPE)
data _≤_ : Env → Env → Set where
  id   : {Γ : Env} → Γ ≤ Γ
  weak : ∀ {A Γ Δ } → (t : Δ ≤ Γ) → Δ , A ≤ Γ
  lift : ∀ {A Γ Δ } → (t : Δ ≤ Γ) → Δ , A ≤ Γ , A

-- OPEs compose
_∙_ : ∀ {Φ Δ Γ} → Φ ≤ Δ → Γ ≤ Φ → Γ ≤ Δ
f      ∙ id = f
f      ∙ weak g = weak (f ∙ g)
id     ∙ lift g = lift g
weak f ∙ lift g = weak (f ∙ g)
lift f ∙ lift g = lift (f ∙ g)

fresh : ∀ {Γ a} → (Γ , a) ≤ Γ
fresh = weak id
