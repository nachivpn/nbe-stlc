module Type where

infixl 5 _+_

data Ty : Set where

  -- unit/terminal type
  𝟙    : Ty

  -- standard type constructors
  _⇒_  : (a b : Ty) → Ty
  _*_  : (a b : Ty) → Ty
  _+_  : (a b : Ty) → Ty

  -- 𝔹ase type
  𝕓    :              Ty

infixl 5 _,_

data Ctx : Set where
  [] : Ctx
  _,_ : (Γ : Ctx) (a : Ty) → Ctx
