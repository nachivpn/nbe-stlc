module Norm where

open import Data.Unit using (tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)

open import NF
open import Dec
open import Type
open import Term
open import Presheaf
open import Thinning

open 𝒫 renaming (F to In ; fmap to wk)

private
  variable
    a b c : Ty
    Γ Δ : Ctx
    A B : 𝒫

-- interpretation of types
⟦_⟧ : Ty → 𝒫
⟦   𝕓   ⟧ = Nf' 𝕓
⟦   𝟙   ⟧ = 𝟙'
⟦ a ⇒ b ⟧ = ⟦ a ⟧ ⇒' ⟦ b ⟧
⟦ a * b ⟧ = ⟦ a ⟧ ×' ⟦ b ⟧
⟦ a + b ⟧ = Dec' (⟦ a ⟧ +' ⟦ b ⟧)

-- interpretation of contexts
⟦_⟧ₑ : Ctx → 𝒫
⟦ [] ⟧ₑ     = 𝟙'
⟦ e `, a ⟧ₑ = ⟦ e ⟧ₑ ×' ⟦ a ⟧

-- special operations on decision trees
module DecOps where

  -- special case of expDec
  mapDec' : In (A ⇒' B) Δ → Dec Δ A → Dec Δ B
  mapDec' f c = expDec f id c

  -- convert decision over normal forms to a normal form
  convertNf : Dec' (Nf' a) →̇ Nf' a
  convertNf (leaf a)       = a
  convertNf (branch x p q) = case x (convertNf p) (convertNf q)

  -- make decision over a semantic value
  mkDec : Dec' ⟦ a ⟧ →̇ ⟦ a ⟧
  mkDec {𝟙}     c         = tt
  mkDec {a * b} c         = mkDec {a} (mapDec proj₁ c) , mkDec {b} (mapDec proj₂ c)
  mkDec {a + b} c         = joinDec c
  mkDec {𝕓}     c         = convertNf c
  mkDec {a ⇒ b} f {Δ} e x = mkDec {b} y
    where
    f' : Dec Δ ⟦ a ⇒ b ⟧
    f' = wkDec e f
    y : Dec Δ ⟦ b ⟧
    y = mapDec' (λ e' g → (g id (⟦ a ⟧ .wk e' x))) f'

open DecOps

-----  THE MEAT!

mutual

  reflect : Ne' a →̇ ⟦ a ⟧
  reflect {𝟙} _     = tt
  reflect {𝕓} b     = lift b
  reflect {a ⇒ b} f = λ e →
    let f' = (wkNe e f)
    in λ x → reflect (app f' (reify x))
  reflect {a * b} t = reflect (fst t) , reflect (snd t)
  reflect {a + b} t =
    branch t
      (leaf (inj₁ (reflect {a} (var zero))))
      (leaf (inj₂ (reflect {b} (var zero))))

  reify : ⟦ a ⟧ →̇  Nf' a
  reify {𝟙} tt           = unit
  reify {𝕓} a            = a
  reify {a ⇒ b} f        = abs (reify (f fresh (reflect {a} (var zero))))
  reify {a * b} (P , Q)  = pair (reify P) (reify Q)
  reify {a + b} t        = convertNf (mapDec reifyOr t)
    where
      reifyOr : (⟦ a ⟧ +' ⟦ b ⟧) →̇ Nf' (a + b)
      reifyOr (inj₁ x) = inl (reify x)
      reifyOr (inj₂ y) = inr (reify y)

-- perform a lookup in the meta language
-- using an index in the object language
lookup : Var Γ a → (⟦ Γ ⟧ₑ →̇  ⟦ a ⟧)
lookup zero (Γ , a)     = a
lookup (succ v) (Γ , _) = lookup v Γ

-- interpret a Tm in the meta theory (in Set)
-- i.e., denotational semantics for (possibly open) Tms
eval : Tm Γ a → ⟦ Γ ⟧ₑ →̇ ⟦ a ⟧
eval (var x) γ         = lookup x γ
eval {Γ} (abs f) γ     = λ e x → eval f (⟦ Γ ⟧ₑ .wk e γ , x)
eval (app f x) γ       = eval f γ id (eval x γ)
eval (pair p q) γ      = (eval p γ) , (eval q γ)
eval unit γ            = tt
eval (fst x) γ         = proj₁ (eval x γ)
eval (snd x) γ         = proj₂ (eval x γ)
eval (inl x) γ         = leaf (inj₁ (eval x γ))
eval (inr x) γ         = leaf (inj₂ (eval x γ))
eval {Γ} {c} (case {a} {b} x p q) {Δ} γ =
  mkDec {c} (mapDec' match (eval x γ))
  where
    match : ((⟦ a ⟧ +' ⟦ b ⟧) ⇒' ⟦ c ⟧) .In Δ
    match e (inj₁ x) = eval p (⟦ Γ ⟧ₑ .wk e γ , x)
    match e (inj₂ y) = eval q (⟦ Γ ⟧ₑ .wk e γ , y)

-- semantics of the identity environment
reflect_env : ∀ (Γ : Ctx) → ⟦ Γ ⟧ₑ .In Γ
reflect_env []       = tt
reflect_env (Γ `, a) =  env' , reflect {a} (var zero)
  where
  -- we weaken the semantics (env Γ)
  -- using the the weakener in the presheaf ⟦ Γ ⟧ₑ
  env' = ⟦ Γ ⟧ₑ .wk fresh (reflect_env Γ)

-- eval lifts a term to an agda term
-- and reify forces evaluation of its argument (the agda term) and uses the
-- result to produce a normal form
norm : Tm' a →̇ Nf' a
norm {_} {Γ} t = reify (eval t (reflect_env Γ))

normalize : Tm Γ a → Tm Γ a
normalize t = emb (norm t)
