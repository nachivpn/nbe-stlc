module Type where

data Ty : Set where

  -- unit/terminal type
  𝟙    : Ty

  -- standard type constructors
  _⇒_  : (a b : Ty) → Ty
  _*_  : (a b : Ty) → Ty
  _+_  : (a b : Ty) → Ty

  -- 𝔹ase type
  𝔹    :              Ty
  
  -- "𝔽ix point type"
  𝔽    : (a   : Ty) → Ty -- semantically, 𝔽 f = f (𝔽 f)


