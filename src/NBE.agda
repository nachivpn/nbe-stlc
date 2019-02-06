{-# OPTIONS --postfix-projections #-}
module NBE where

open import Type
open import Lambda renaming (_,_ to _`,_)

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
    var : ∀ {A}   → Var Γ A      → Ne Γ A
    app : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    fst : ∀ {A B} → Ne Γ (A * B) → Ne Γ A
    snd : ∀ {A B} → Ne Γ (A * B) → Ne Γ B
  
  -- Normal forms are terms which cannot be reduced further
  data Nf (Γ : Env) : Ty → Set where
    abs  : ∀ {A B}   → Nf (Γ `, A) B → Nf Γ (A ⇒ B)
    pair : ∀ {A B}   → Nf Γ A → Nf Γ B → Nf Γ (A * B)
    -- TODO description of these promoters
    neb+ :             Ne Γ 𝔹 →  Nf Γ 𝔹
    unit :             Nf Γ 𝟙
    inl  : ∀ {A B}   → Nf Γ A → Nf Γ (A + B)
    inr  : ∀ {A B}   → Nf Γ B → Nf Γ (A + B)
    case : ∀ {A B C} → Ne Γ (A + B) → Nf (Γ `, A) C → Nf (Γ `, B) C → Nf Γ C
    
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

mutual
  -- weaken a normal form
  nfₑ : ∀ {Γ Δ A} → Δ ≤ Γ → Nf Γ A  → Nf Δ A
  nfₑ e (abs n)      = abs (nfₑ (lift e) n)
  nfₑ e (pair p q)   = pair (nfₑ e p) (nfₑ e q)
  nfₑ e unit         = unit
  nfₑ e (inl x)      = inl (nfₑ e x)
  nfₑ e (inr x)      = inr (nfₑ e x)
  nfₑ e (case x p q) = case (neₑ e x) (nfₑ (lift e) p) (nfₑ (lift e) q)
  nfₑ e (neb+ x)     = neb+ (neₑ e x)

  -- weaken a neutral form
  neₑ : ∀ {Γ Δ A} → Δ ≤ Γ → Ne Γ A  → Ne Δ A
  neₑ e (var x)   = var (varₑ e x)
  neₑ e (app n x) = app (neₑ e n) (nfₑ e x)
  neₑ e (fst x)   = fst (neₑ e x)
  neₑ e (snd x)   = snd (neₑ e x)
  

open import Data.Unit using (tt)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Presheaf
open 𝒫

-- presheafs indexed by a type
module IndexedPresheafs where
  
  Var' : (A : Ty) → 𝒫
  Var' A .𝒪 Γ = Var Γ A
  Var' A .ℱ   = varₑ
  
  Ne' : (A : Ty) → 𝒫
  Ne' A .𝒪 Γ = Ne Γ A
  Ne' A .ℱ   = neₑ    
  
  Tm' : (A : Ty) → 𝒫
  Tm' A .𝒪 Γ = Tm Γ A
  Tm' A .ℱ   = tmₑ

  Nf' : (A : Ty) → 𝒫
  Nf' A .𝒪 Γ = Nf Γ A
  Nf' A .ℱ   = nfₑ

  -- components of a natural transformation which maps
  -- variable preasheafs to neutral presheafs
  var2ne : ∀ {A : Ty} → Var' A →̇ Ne' A
  var2ne = var

open IndexedPresheafs

module CoverMonad where

  data Cover (Γ : Env) (A : 𝒫) : Set where
    retC  : (a : 𝒪 A Γ) →  Cover Γ A
    caseC : ∀{C D} → Ne Γ (C + D) → Cover (Γ `, C) A →  Cover (Γ `, D) A → Cover Γ A

  coverₑ : ∀ {Γ Δ A} → Δ ≤ Γ → Cover Γ A  → Cover Δ A
  coverₑ {A = A} e (retC a)      = retC (A .ℱ e a)
  coverₑ {A = A} e (caseC x p q) =
    caseC ((Ne' _) .ℱ e x)
      (coverₑ (lift e) p)
      (coverₑ (lift e) q)

  -- Cover' is an endofunctor on category of presheaves (construction and properties below)
    
  -- object map of Cover'
  Cover' : (A : 𝒫) → 𝒫
  Cover' A .𝒪 Γ = Cover Γ A
  Cover' A .ℱ   = coverₑ
  
  -- morphism map of Cover'
  liftC : ∀ {A B : 𝒫} → (A →̇ B) → (Cover' A →̇ Cover' B)
  liftC t (retC a) = retC (t a)
  liftC t (caseC x p q) = caseC x (liftC t p) (liftC t q)

  -- Cover' is an "idempotent" functor
  joinC : ∀{A} → Cover' (Cover' A) →̇ Cover' A
  joinC (retC a) = a
  joinC (caseC x p q) = caseC x (joinC p) (joinC q)

  -- joinC is an isomorphism
  joinC⁻¹ : ∀{A} → Cover' A →̇ Cover' (Cover' A)
  joinC⁻¹ = retC

  -- a morphism from an exponential to an exponential of it's covered components
  -- i.e., (b ^ a) →̇ (Cover' b) ^ (Cover' a)
  expC :  ∀ {A B : 𝒫} → (A ⇒' B) →̇ (Cover' A ⇒' Cover' B)
  expC f τ (retC a) = retC (f τ a)
  expC f τ (caseC x c₁ c₂) = caseC x (expC f (weak τ) c₁) (expC f (weak τ) c₂)
  
open CoverMonad

-- assign semantics to types and environments using presheafs
module PresheafSemantics where

  ⟦_⟧ : Ty → 𝒫
  ⟦   𝟙   ⟧ = 𝟙'
  ⟦ A ⇒ B ⟧ = ⟦ A ⟧ ⇒' ⟦ B ⟧
  ⟦ A * B ⟧ = ⟦ A ⟧ ×' ⟦ B ⟧
  ⟦ A + B ⟧ = Cover' (⟦ A ⟧ +' ⟦ B ⟧)
  ⟦   𝔹   ⟧ = Nf' 𝔹

  ⟦_⟧ₑ : Env → 𝒫
  ⟦ [] ⟧ₑ = 𝟙'
  ⟦ e `, a ⟧ₑ = ⟦ e ⟧ₑ ×' ⟦ a ⟧
  
open PresheafSemantics

-- special cover operations
module CoverOps where
  
  -- special case of liftExpC
  mapC : ∀ {A B Δ} → 𝒪 (A ⇒' B) Δ → Cover Δ A → Cover Δ B
  mapC f c = expC f id c

  -- cover preserves normal forms
  unCoverNf : ∀{A} → Cover' (Nf' A) →̇ Nf' A
  unCoverNf (retC a)       = a
  unCoverNf (caseC x p q) = case x (unCoverNf p) (unCoverNf q)

  -- cover preserves preserves 
  unCover : ∀{A} → Cover' ⟦ A ⟧ →̇ ⟦ A ⟧
  unCover {𝟙}     c         = tt
  unCover {A * B} c         = unCover {A} (liftC proj₁ c) , unCover {B} (liftC proj₂ c)
  unCover {A + B} c         = joinC c
  unCover {𝔹}     c         = unCoverNf c
  unCover {A ⇒ B} f {Δ} τ a = unCover {B} b'
    where
    f' : Cover Δ ⟦ A ⇒ B ⟧
    f' = (Cover' _) .ℱ τ f
    b' : Cover Δ ⟦ B ⟧
    b' = mapC (λ δ g → (g id (⟦ A ⟧ .ℱ δ a))) f'
  
open CoverOps
 
-----  THE MEAT!

mutual
  reflect :  ∀ {A : Ty} → Ne' A →̇ ⟦ A ⟧
  reflect {𝟙} _     = tt
  reflect {𝔹} b     = neb+ b
  reflect {A ⇒ B} f = λ τ →
    let f' = (ℱ (Ne' (A ⇒ B)) τ f)
    in λ x → reflect (app f' (reify x))
  reflect {A * B} t = reflect (fst t) , reflect (snd t)
  reflect {A + B} t =
    caseC t
      (retC (inj₁ (reflect {A} (var zero))))
      (retC (inj₂ (reflect {B} (var zero))))

  reify :  ∀ {A : Ty} → ⟦ A ⟧ →̇  Nf' A
  reify {𝟙} tt           = unit
  reify {𝔹} a            = a
  reify {A ⇒ B} f        = abs (reify (f (weak id) (reflect {A} (var zero))))
  reify {A * B} (P , Q)  = pair (reify P) (reify Q)
  reify {A + B} t        = unCoverNf (liftC reifyOr t)
    where
      reifyOr : ∀ {A B} → (⟦ A ⟧ +' ⟦ B ⟧) →̇ Nf' (A + B)
      reifyOr (inj₁ x) = inl (reify x)
      reifyOr (inj₂ y) = inr (reify y)   

-- perform a lookup in the meta language
-- using an index in the object language
lookup : ∀{Γ A} → Var Γ A → (⟦ Γ ⟧ₑ →̇  ⟦ A ⟧)
lookup zero (Γ , a)     = a
lookup (succ v) (Γ , _) = lookup v Γ

-- interpret a Tm in the meta theory (in Set)
-- i.e., denotational semantics for (possibly open) Tms
eval : ∀ {A Γ} → Tm Γ A → ⟦ Γ ⟧ₑ →̇ ⟦ A ⟧
eval (var x) γ         = lookup x γ
eval {_} {Γ} (abs f) γ = λ τ x → eval f (⟦ Γ ⟧ₑ .ℱ τ γ , x)
eval (app f x) γ       = eval f γ id (eval x γ)
eval (pair p q) γ      = (eval p γ) , (eval q γ)
eval unit γ            = tt
eval (fst x) γ         = proj₁ (eval x γ)
eval (snd x) γ         = proj₂ (eval x γ)
eval (inl x) γ         = retC (inj₁ (eval x γ))
eval (inr x) γ         = retC (inj₂ (eval x γ))
eval {C} {Γ} (case {A} {B} x p q) {Δ} γ =
  unCover {C} (mapC match (eval x γ))
  where
    match : 𝒪 ((⟦ A ⟧ +' ⟦ B ⟧) ⇒' ⟦ C ⟧) Δ
    match τ (inj₁ x) = eval p (⟦ Γ ⟧ₑ .ℱ τ γ , x)
    match τ (inj₂ y) = eval q (⟦ Γ ⟧ₑ .ℱ τ γ , y)
      
-- semantics of the identity environment
reflect_env : ∀ (Γ : Env) → ⟦ Γ ⟧ₑ .𝒪 Γ
reflect_env []       = tt
reflect_env (Γ `, A) =  env' , reflect {A} (var zero)
  where
  -- we weaken the semantics (env Γ)
  -- using the the weakener in the presheaf ⟦ Γ ⟧ₑ
  env' = ⟦ Γ ⟧ₑ .ℱ (weak id) (reflect_env Γ)

-- eval lifts a term to an agda term
-- and reify forces evaluation of its argument (the agda term) and uses the
-- result to produce a normal form
norm : ∀ {A : Ty} → Tm' A →̇ Nf' A
norm {A} {Γ} t = reify (eval t (reflect_env Γ))

-- See, I told you! ' →̇ ' is just a way make (Γ : Env) implicit
normalize : ∀ {Γ : Env} {A : Ty} → Tm Γ A → Nf Γ A
normalize = norm
