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
  𝔹    :              Ty
  
  -- "𝔽ixed point" type
  -- A term of type (𝔽 a) is a recursive computation
  -- of a value of type a
  𝔽    : (a   : Ty) → Ty

