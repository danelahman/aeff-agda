open import Data.Product

open import Operations

module Types where

postulate BType : Set -- set of base types

GType = BType

mutual
  data VType : Set where
    G   : GType → VType
    _⇒_ : VType → CType → VType
    ⟨_⟩ : VType → VType

  data CType : Set where
    _!_ : VType → O × I → CType

infix 30 _⇒_
infix 30 _!_
