-- Simple NBE for a simple lambda calculus with finite products and base types

data Ty : Set where
  𝟙    : Ty
  𝕓    : Ty
  _⇒_  : (a b : Ty) → Ty
  _*_  : (a b : Ty) → Ty

data Env : Set where
  []   : Env
  _`,_ : (Γ : Env) (a : Ty) → Env

data Var : Env → Ty → Set where
  zero : ∀ {Γ A}   → Var (Γ `, A) A
  succ : ∀ {Γ A B} → Var Γ A → Var (Γ `, B) A

data Tm (Γ : Env) : Ty → Set where
  unit : Tm Γ 𝟙  
  var  : ∀ {A}   → Var Γ A → Tm Γ A
  abs  : ∀ {A B} → Tm (Γ `, A) B → Tm Γ (A ⇒ B)
  app  : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  pair : ∀ {A B} → Tm Γ A → Tm Γ B → Tm Γ (A * B)
  fst  : ∀ {A B} → Tm Γ (A * B) → Tm Γ A
  snd  : ∀ {A B} → Tm Γ (A * B) → Tm Γ B

mutual

  data Ne (Γ : Env) : Ty → Set where
    var : ∀ {A}   → Var Γ A      → Ne Γ A
    app : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    fst : ∀ {A B} → Ne Γ (A * B) → Ne Γ A
    snd : ∀ {A B} → Ne Γ (A * B) → Ne Γ B
    
  data Nf (Γ : Env) : Ty → Set where
    unit : Nf Γ 𝟙
    ne+  : Ne Γ 𝕓 →  Nf Γ 𝕓
    abs  : ∀ {A B} → Nf (Γ `, A) B → Nf Γ (A ⇒ B)
    pair : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A * B)

open import Data.Unit using (⊤ ; tt)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)

data _≤_ : Env → Env → Set where
  id   : {T : Env} → T ≤ T
  weak : ∀ {S T A} → S ≤ T → (S `, A) ≤ T  
  lift : ∀ {S T A} → S ≤ T → (S `, A) ≤ (T `, A)

_∙_ : ∀ {Φ Δ Γ} → Φ ≤ Δ → Γ ≤ Φ → Γ ≤ Δ
f      ∙ id = f
f      ∙ weak g = weak (f ∙ g)
id     ∙ lift g = lift g
weak f ∙ lift g = weak (f ∙ g)
lift f ∙ lift g = lift (f ∙ g)

-- semantics for types
Sem : (Γ : Env) → Ty →  Set
Sem Γ 𝟙        = ⊤
Sem Γ (t ⇒ t₁) = ∀ {Δ} → Δ ≤ Γ → Sem Δ t → Sem Δ t₁
Sem Γ (t * t₁) = Sem Γ t × Sem Γ t₁
Sem Γ 𝕓        = Ne Γ 𝕓 -- This require Sem to be indexed over Env

-- semantics for env, indexed by an env (required for Sem)
Semₑ : Env → Env → Set
Semₑ _ []        = ⊤
Semₑ Γ (e `, a ) = Semₑ Γ e × Sem Γ a

module Weakenings where

  wkVar : ∀{a e e'} → e' ≤ e → Var e a →  Var e' a
  wkVar id v              = v
  wkVar (weak τ) v        = succ (wkVar τ v)
  wkVar (lift τ) zero     = zero
  wkVar (lift τ) (succ v) = succ (wkVar τ v)

  mutual

    wkNe : ∀{a e e'} → e' ≤ e → Ne e a →  Ne e' a
    wkNe τ (var x)    = var (wkVar τ x)
    wkNe τ (app x x₁) = app (wkNe τ x) (wkNf τ x₁)
    wkNe τ (fst x)    = fst (wkNe τ x)
    wkNe τ (snd x)    = snd (wkNe τ x)

    wkNf : ∀{a e e'} → e' ≤ e → Nf e a →  Nf e' a
    wkNf τ unit        = unit
    wkNf τ (ne+ x)     = ne+ (wkNe τ x)
    wkNf τ (abs n)     = abs (wkNf (lift τ) n)
    wkNf τ (pair n n₁) = pair (wkNf τ n) (wkNf τ n₁)

  wkSem : ∀{a e e'} → e' ≤ e → Sem e a →  Sem e' a
  wkSem {𝟙} τ s            = tt
  wkSem {𝕓} τ s            = wkNe τ s
  wkSem {_ ⇒ _}  τ f τ' a  = f (τ ∙ τ') a
  wkSem {a * a₁} τ (p , q) = (wkSem τ p) , (wkSem τ q)

  wkSemₑ : ∀{a e' e} → e' ≤ e → Semₑ e a →  Semₑ e' a
  wkSemₑ {[]}     τ s       = tt
  wkSemₑ {_ `, _} τ (e , a) = (wkSemₑ τ e) , wkSem τ a

open Weakenings

mutual

  -- reflect neutral terms into semantics
  reflect : ∀ {Γ} (A : Ty) → Ne Γ A → Sem Γ A
  reflect 𝟙       _ = tt
  reflect (A ⇒ B) t = λ τ a → reflect B (app (wkNe τ t) (reify a))
  reflect (A * B) t = reflect A (fst t), reflect B (snd t)
  reflect 𝕓       t = t

  -- reify semantics into normal forms
  reify :  ∀ {A Γ} → Sem Γ A → Nf Γ A
  reify {𝟙}     t  = unit
  reify {A ⇒ B} t  = abs (reify (t (weak id) (reflect A (var zero))))
  reify {A * B} t  = pair (reify (proj₁ t)) (reify (proj₂ t))
  reify {𝕓}     t  = ne+ t

-- evaluate a lambda term into semantics
-- can be viewed as an interpreter
eval :  ∀ {A Γ} → Tm Γ A → Sem Γ A
eval {Γ = Γ} t = eval' t (reflectₑ Γ)
  where
  
  -- use variables to project the environment
  lookup : ∀{Γ Γ' A} → Var Γ A → Semₑ Γ' Γ →  Sem Γ' A
  lookup zero     (Γ , a) = a
  lookup (succ v) (Γ , _) = lookup v Γ

  eval' : ∀ {A Γ} → Tm Γ A → ∀ {Γ'} → Semₑ Γ' Γ → Sem Γ' A
  eval' unit    ρ     = tt
  eval' (var x) ρ     = lookup x ρ
  eval' (abs t) ρ     = λ τ' a → eval' t (wkSemₑ τ' ρ , a)
  eval' (app t t₁) ρ  = eval' t ρ id (eval' t₁ ρ)
  eval' (pair t t₁) ρ = (eval' t ρ) , (eval' t₁ ρ)
  eval' (fst t) ρ     = proj₁ (eval' t ρ)
  eval' (snd t) ρ     = proj₂ (eval' t ρ)
  
  -- produces a semantic value for the given environment
  reflectₑ : (Γ : Env) → Semₑ Γ Γ
  reflectₑ [] = tt
  reflectₑ (e `, a) = wkSemₑ (weak id) (reflectₑ e) , reflect a (var zero)

open import Function

-- evaluate the term into semantics by reflecting the env
-- reify the semantic value into a normal form
norm : ∀ {A Γ} → Tm Γ A → Nf Γ A
norm = reify ∘ eval
