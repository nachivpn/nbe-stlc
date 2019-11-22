module Thinning where

open import Type

infix 4 _≤_

private
  variable
    Γ Δ Σ : Ctx
    a b : Ty

-- Order Preserving Embedding (OPE)
data _≤_ : Ctx → Ctx → Set where
  id   : Γ ≤ Γ
  weak : (t : Δ ≤ Γ) → Δ `, a ≤ Γ
  lift : (t : Δ ≤ Γ) → Δ `, a ≤ Γ `, a

-- OPEs compose
_∙_ : Σ ≤ Δ → Γ ≤ Σ → Γ ≤ Δ
f      ∙ id = f
f      ∙ weak g = weak (f ∙ g)
id     ∙ lift g = lift g
weak f ∙ lift g = weak (f ∙ g)
lift f ∙ lift g = lift (f ∙ g)

fresh : (Γ `, a) ≤ Γ
fresh = weak id
