module Type where

data Ty : Set where
  𝟙    : Ty
  _⇒_  : (a b : Ty) → Ty  
  _*_  : (a b : Ty) → Ty
  _+_  : (a b : Ty) → Ty
