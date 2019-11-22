module Dec where

open import NF
open import Type
open import Presheaf
open import Thinning
open 𝒫 renaming (F to In ; fmap to wk)

private
  variable
    a b c d : Ty
    Γ Δ : Ctx
    A B : 𝒫

data Dec (Γ : Ctx) (A : 𝒫) : Set where
  leaf  : (a : In A Γ) →  Dec Γ A
  branch : Ne Γ (c + d) → Dec (Γ `, c) A →  Dec (Γ `, d) A → Dec Γ A

wkDec : Δ ≤ Γ → Dec Γ A  → Dec Δ A
wkDec {A = A} e (leaf a)      = leaf (A .wk e a)
wkDec {A = A} e (branch x p q) =
  branch (wkNe e x)
    (wkDec (lift e) p)
    (wkDec (lift e) q)

-- Dec' is an endofunctor on category of presheaves (construction and properties below)

-- object map of Dec'
Dec' : (A : 𝒫) → 𝒫
Dec' A .In Γ = Dec Γ A
Dec' A .wk   = wkDec

-- morphism map of Dec'
mapDec : (A →̇ B) → (Dec' A →̇ Dec' B)
mapDec t (leaf a) = leaf (t a)
mapDec t (branch x p q) = branch x (mapDec t p) (mapDec t q)

-- Dec' is an "idempotent" functor
joinDec : Dec' (Dec' A) →̇ Dec' A
joinDec (leaf a) = a
joinDec (branch x p q) = branch x (joinDec p) (joinDec q)

cojoinDec : Dec' A →̇ Dec' (Dec' A)
cojoinDec = leaf

-- a morphism from an exponential to an exponential of it's covered components
-- i.e., (b ^ a) →̇ (Dec' b) ^ (Dec' a)
expDec :  (A ⇒' B) →̇ (Dec' A ⇒' Dec' B)
expDec f τ (leaf a) = leaf (f τ a)
expDec f τ (branch x c₁ c₂) = branch x (expDec f (weak τ) c₁) (expDec f (weak τ) c₂)
