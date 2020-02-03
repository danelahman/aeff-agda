open import Data.Product

open import Operations

module Types where

postulate BType : Set -- set of base types

GType = BType

mutual
  data VType : Set where
    ground  : GType → VType
    arrow   : VType → CType → VType
    promise : VType → VType

  data CType : Set where
    _!_ : VType → O × I → CType

infix 30 _!_
