module Term where

open import Type
open import Thinning
open import Presheaf
open 𝒫 renaming (F to In ; fmap to wk)

private
  variable
    Γ Δ Σ : Ctx
    a b c : Ty

data Var : Ctx → Ty → Set where
  zero : Var (Γ `, a) a
  succ : Var Γ a → Var (Γ `, b) a

data Tm (Γ : Ctx) : Ty → Set where
  var  : Var Γ a → Tm Γ a

  abs  : Tm (Γ `, a) b
       --------------
       → Tm Γ (a ⇒ b)

  app  : Tm Γ (a ⇒ b) → Tm Γ a
       -----------------------
       → Tm Γ b

  pair : Tm Γ a → Tm Γ b
       -----------------
       → Tm Γ (a * b)

  unit : Tm Γ 𝟙

  fst  : Tm Γ (a * b)
       --------------
       → Tm Γ a

  snd  : Tm Γ (a * b)
       --------------
       → Tm Γ b

  inl  : Tm Γ a
       --------------
       → Tm Γ (a + b)

  inr  : Tm Γ b
       --------------
       → Tm Γ (a + b)

  case : Tm Γ (a + b) → Tm (Γ `, a) c → Tm (Γ `, b) c
       --------------------------------------------
       → Tm Γ c

-- weaken a variable with a thinning
wkVar : Δ ≤ Γ → Var Γ a →  Var Δ a
wkVar id x              = x
wkVar (weak e) x        = succ (wkVar e x)
wkVar (lift e) zero     = zero
wkVar (lift e) (succ x) = succ (wkVar e x)

-- weaken a term with a thinning
wkTm : Δ ≤ Γ → Tm Γ a  → Tm Δ a
wkTm e (var x)        = var (wkVar e x)
wkTm e (abs t)        = abs (wkTm (lift e) t)
wkTm e (app f x)      = app (wkTm e f) (wkTm e x)
wkTm e (pair x y)     = pair (wkTm e x) (wkTm e y)
wkTm e unit           = unit
wkTm e (fst t)        = fst (wkTm e t)
wkTm e (snd t)        = snd (wkTm e t)
wkTm e (inl t)        = inl (wkTm e t)
wkTm e (inr t)        = inr (wkTm e t)
wkTm e (case x f g)   = case (wkTm e x) (wkTm (lift e) f) (wkTm (lift e) g)

private

  -- as an EXAMPLE of need for term embedding, consider eta expansion
  eta : Tm Γ (a ⇒ b) → Tm Γ (a ⇒ b)
  eta f = abs (app (wkTm (weak id) f) (var zero))


Var' : (a : Ty) → 𝒫
Var' a .In Γ = Var Γ a
Var' a .wk   = wkVar

Tm' : (a : Ty) → 𝒫
Tm' a .In Γ = Tm Γ a
Tm' a .wk   = wkTm
