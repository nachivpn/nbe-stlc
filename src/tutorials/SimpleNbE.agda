-- Ridiculously simple NBE for a ridiculously simple lambda calculus with finite products

data Ty : Set where
  𝟙    : Ty
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

-- normal forms obey subformula property, and are easily embedded back into terms
data Nf (Γ : Env) : Ty → Set where
  unit : Nf Γ 𝟙
  abs  : ∀ {A B} → Nf (Γ `, A) B → Nf Γ (A ⇒ B)
  pair : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A * B)

open import Data.Unit using (⊤ ; tt)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)

-- semantics for types
⟦_⟧ : Ty → Set
⟦ 𝟙 ⟧      = ⊤
⟦ t ⇒ t₁ ⟧ = ⟦ t ⟧ → ⟦ t₁ ⟧
⟦ t * t₁ ⟧ = ⟦ t ⟧ × ⟦ t₁ ⟧

-- semantics for env
⟦_⟧ₑ : Env → Set
⟦ [] ⟧ₑ     = ⊤
⟦ e `, a ⟧ₑ = ⟦ e ⟧ₑ × ⟦ a ⟧

-- reflection doesn't need a (neutral) term, the type alone is enough!
-- this is because a type is so ridiculously simple that it has only one inhabitant
reflect : ∀ (A : Ty) → ⟦ A ⟧
reflect 𝟙       = tt
reflect (A ⇒ B) = λ x → reflect B
reflect (A * B) = reflect A , reflect B

-- produces a semantic value for the given environment
reflectₑ : (Γ : Env) → ⟦ Γ ⟧ₑ
reflectₑ [] = tt
reflectₑ (e `, a) = reflectₑ e , reflect a

-- type directed reification, because we cannot always inspect a semantic value
reify :  ∀ {A Γ} → ⟦ A ⟧ → Nf Γ A
reify {𝟙}      t = unit
reify {A ⇒ B} t = abs (reify (t (reflect A)))
reify {A * B} t = pair (reify (proj₁ t)) (reify (proj₂ t))  

-- use variables to project the environment
lookup : ∀{Γ A} → Var Γ A → ⟦ Γ ⟧ₑ →  ⟦ A ⟧
lookup zero     (Γ , a) = a
lookup (succ v) (Γ , _) = lookup v Γ

-- evaluate a lambda term into semantics
-- can be viewed as an interpreter
eval :  ∀ {A Γ} → Tm Γ A → (⟦ Γ ⟧ₑ → ⟦ A ⟧)
eval (var x) e    = lookup x e
eval (abs t) e    = λ x → eval t (e , x)
eval (app s t) e  = eval s e (eval t e)
eval (pair s t) e = (eval s e) , (eval t e)
eval unit e       = tt
eval (fst t) e    = proj₁ (eval t e)
eval (snd t) e    = proj₂ (eval t e)

-- evaluate the term into semantics by reflecting the env
-- reify the semantic value into a normal form
norm : ∀ {A Γ} → Tm Γ A → Nf Γ A
norm {A} {Γ} t = reify (eval t (reflectₑ Γ))
