module NBE where

open import Data.Unit using (tt)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Type
open import Presheaf
open 𝒫 renaming (F to In ; fmap to wk)
open import Lambda renaming (_,_ to _`,_)

variable
  Γ Δ : Env
  a b c : Ty
  A B : 𝒫

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
  data Ne (Γ : Env) : Ty → Set where
    var : Var Γ a      → Ne Γ a
    app : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b
    fst : Ne Γ (a * b) → Ne Γ a
    snd : Ne Γ (a * b) → Ne Γ b

  -- Normal forms are terms which cannot be reduced further
  data Nf (Γ : Env) : Ty → Set where
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

open import OPE

-- variable embedding
wkVar : Δ ≤ Γ → Var Γ a →  Var Δ a
wkVar id x              = x
wkVar (weak e) x        = succ (wkVar e x)
wkVar (lift e) zero     = zero
wkVar (lift e) (succ x) = succ (wkVar e x)

-- term embedding
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

-- presheafs indexed by a type
module IndexedPresheafs where

  Var' : (a : Ty) → 𝒫
  Var' a .In Γ = Var Γ a
  Var' a .wk   = wkVar

  Ne' : (a : Ty) → 𝒫
  Ne' a .In Γ = Ne Γ a
  Ne' a .wk   = wkNe

  Tm' : (a : Ty) → 𝒫
  Tm' a .In Γ = Tm Γ a
  Tm' a .wk   = wkTm

  Nf' : (a : Ty) → 𝒫
  Nf' a .In Γ = Nf Γ a
  Nf' a .wk   = wkNf

open IndexedPresheafs

module DecMonad where

  data Dec (Γ : Env) (A : 𝒫) : Set where
    leaf  : (a : In A Γ) →  Dec Γ A
    branch : ∀{C D} → Ne Γ (C + D) → Dec (Γ `, C) A →  Dec (Γ `, D) A → Dec Γ A

  wkDec : Δ ≤ Γ → Dec Γ A  → Dec Δ A
  wkDec {A = A} e (leaf a)      = leaf (A .wk e a)
  wkDec {A = A} e (branch x p q) =
    branch ((Ne' _) .wk e x)
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

open DecMonad

-- assign semantics to types and environments using presheafs
module PresheafSemantics where

  ⟦_⟧ : Ty → 𝒫
  ⟦   𝟙   ⟧ = 𝟙'
  ⟦ A ⇒ B ⟧ = ⟦ A ⟧ ⇒' ⟦ B ⟧
  ⟦ A * B ⟧ = ⟦ A ⟧ ×' ⟦ B ⟧
  ⟦ A + B ⟧ = Dec' (⟦ A ⟧ +' ⟦ B ⟧)
  ⟦   𝕓   ⟧ = Nf' 𝕓

  ⟦_⟧ₑ : Env → 𝒫
  ⟦ [] ⟧ₑ = 𝟙'
  ⟦ e `, a ⟧ₑ = ⟦ e ⟧ₑ ×' ⟦ a ⟧

open PresheafSemantics

-- special cover operations
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
  reflect {a ⇒ b} f = λ τ →
    let f' = (wkNe τ f)
    in λ x → reflect (app f' (reify x))
  reflect {A * B} t = reflect (fst t) , reflect (snd t)
  reflect {A + B} t =
    branch t
      (leaf (inj₁ (reflect {A} (var zero))))
      (leaf (inj₂ (reflect {B} (var zero))))

  reify : ⟦ a ⟧ →̇  Nf' a
  reify {𝟙} tt           = unit
  reify {𝕓} a            = a
  reify {A ⇒ B} f        = abs (reify (f fresh (reflect {A} (var zero))))
  reify {A * B} (P , Q)  = pair (reify P) (reify Q)
  reify {A + B} t        = convertNf (mapDec reifyOr t)
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
eval {Γ} (abs f) γ = λ τ x → eval f (⟦ Γ ⟧ₑ .wk τ γ , x)
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
    match : In ((⟦ a ⟧ +' ⟦ b ⟧) ⇒' ⟦ c ⟧) Δ
    match τ (inj₁ x) = eval p (⟦ Γ ⟧ₑ .wk τ γ , x)
    match τ (inj₂ y) = eval q (⟦ Γ ⟧ₑ .wk τ γ , y)

-- semantics of the identity environment
reflect_env : ∀ (Γ : Env) → ⟦ Γ ⟧ₑ .In Γ
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

-- See, I told you! ' →̇ ' is just a way make (Γ : Env) implicit
normalize : Tm Γ a → Nf Γ a
normalize = norm
