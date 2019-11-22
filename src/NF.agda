module NF where

open import Type
open import Term
open import Thinning
open import Presheaf
open 𝒫 renaming (F to In ; fmap to wk)

private
  variable
    a b c : Ty
    Γ Δ : Ctx

mutual

  {-
    Neutral terms are "blocked" terms in normal form i.e.,
    neutral terms are variables or eliminators which cannot be reduced further
    For example,
      - Γ ⊢ (var zero) is blocked
      - Γ ⊢ (app (var zero) unit) is blocked
    Neutral terms can be safely substituted for a variable
    without creating a possibility of further reduction.
  -}
  data Ne (Γ : Ctx) : Ty → Set where
    var : Var Γ a      → Ne Γ a
    app : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b
    fst : Ne Γ (a * b) → Ne Γ a
    snd : Ne Γ (a * b) → Ne Γ b

  -- Normal forms are terms which cannot be reduced further
  data Nf (Γ : Ctx) : Ty → Set where
    abs  : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
    pair : Nf Γ a → Nf Γ b → Nf Γ (a * b)
    -- TODO description of these promoters
    lift : Ne Γ 𝕓 →  Nf Γ 𝕓
    unit : Nf Γ 𝟙
    inl  : Nf Γ a → Nf Γ (a + b)
    inr  : Nf Γ b → Nf Γ (a + b)
    case : Ne Γ (a + b) → Nf (Γ `, a) c → Nf (Γ `, b) c → Nf Γ c

  {-
    A note on `case` being in Nf:
    - Even though a case is an eliminator (of a coproduct),
      note that it ends up in normal form rather than neutral.
      This is because we do not want a nested case expression
      in the first argument (had they been in neutral, this would
      have been possible!), and instead be pushed into its branches
      (possibly to trigger further reductions), and this is precisely what the
      current definition allows.

    - because of case being here, normal forms are not unique due
      to the case ordering problem:
      for example,
        case 𝟘 (case 𝟙 n₁ n₂) (case 𝟙 m₁ m₂) ≈
        case 𝟙 (case 𝟘 n₁ m₁) (case 𝟘 n₂ m₂)
      where and n₁,n₂,m₁,m₂ are distinct normal forms
      and ≈ is the βη-equivalence
  -}

mutual

  -- weaken a normal form
  wkNf : Δ ≤ Γ → Nf Γ a  → Nf Δ a
  wkNf e (abs n)      = abs (wkNf (lift e) n)
  wkNf e (pair p q)   = pair (wkNf e p) (wkNf e q)
  wkNf e unit         = unit
  wkNf e (inl x)      = inl (wkNf e x)
  wkNf e (inr x)      = inr (wkNf e x)
  wkNf e (case x p q) = case (wkNe e x) (wkNf (lift e) p) (wkNf (lift e) q)
  wkNf e (lift x)     = lift (wkNe e x)

  -- weaken a neutral form
  wkNe : Δ ≤ Γ → Ne Γ a  → Ne Δ a
  wkNe e (var x)   = var (wkVar e x)
  wkNe e (app n x) = app (wkNe e n) (wkNf e x)
  wkNe e (fst x)   = fst (wkNe e x)
  wkNe e (snd x)   = snd (wkNe e x)

mutual

  emb : Nf Γ a → Tm Γ a
  emb (abs n)      = abs (emb n)
  emb (pair m n)   = pair (emb m) (emb n)
  emb (lift x)     = embNe x
  emb unit         = unit
  emb (inl n)      = inl (emb n)
  emb (inr n)      = inr (emb n)
  emb (case x m n) = case (embNe x) (emb m) (emb n)

  embNe : Ne Γ a → Tm Γ a
  embNe (var x)   = var x
  embNe (app n m) = app (embNe n) (emb m)
  embNe (fst n)   = fst (embNe n)
  embNe (snd n)   = snd (embNe n)


Ne' : (a : Ty) → 𝒫
Ne' a .In Γ = Ne Γ a
Ne' a .wk   = wkNe

Nf' : (a : Ty) → 𝒫
Nf' a .In Γ = Nf Γ a
Nf' a .wk   = wkNf
