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

-- variable embedding
varₑ : ∀ {Γ Δ A} → Δ ≤ Γ → Var Γ A →  Var Δ A
varₑ id x              = x
varₑ (weak e) x        = succ (varₑ e x)
varₑ (lift e) zero     = zero
varₑ (lift e) (succ x) = succ (varₑ e x)

-- term embedding
tmₑ : ∀ {Γ Δ A} → Δ ≤ Γ → Tm Γ A  → Tm Δ A
tmₑ e (var x)        = var (varₑ e x)
tmₑ e (abs t)        = abs (tmₑ (lift e) t)
tmₑ e (app f x)      = app (tmₑ e f) (tmₑ e x)
tmₑ e (pair x y)     = pair (tmₑ e x) (tmₑ e y)
tmₑ e unit           = unit
tmₑ e (fst t)        = fst (tmₑ e t)
tmₑ e (snd t)        = snd (tmₑ e t)
tmₑ e (inl t)        = inl (tmₑ e t)
tmₑ e (inr t)        = inr (tmₑ e t)
tmₑ e (case x f g)   = case (tmₑ e x) (tmₑ (lift e) f) (tmₑ (lift e) g)
tmₑ e (fix f)        = fix (tmₑ e f)

module _ where

  -- as an EXAMPLE of need for term embedding, consider eta expansion
  eta : ∀ {A B Γ}  → Tm Γ (A ⇒ B) → Tm Γ (A ⇒ B)
  eta f = abs (app (tmₑ (weak id) f) (var zero))

  -- OPE is a category given by:
  -- obj = Env
  -- _⇒_ = _≤_
  -- _∘_ = _∙_
  -- _=_ = (recursive syntactic equality)

  -- id ∘ f = f (by induction on f)
  -- f ∘ id = f (be defn of ∙)
  -- (f ∘ g) ∙ h =?= f ∘ (g ∘ h) (todo)


  {-
    The difference between renaming and tmₑ is that
    renaming allows permuting the order of types in the environment
    such as Tm (A  , B) A can be made a Tm (B , A) A
    you _cannot_ create an OPE ([] , A , B) ≤ ([] , B , A)
  -}
