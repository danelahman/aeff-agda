open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality)
open import Relation.Nullary
open import Relation.Nullary.Negation

open import EffectAnnotations

module Types where

-- BASE AND GROUND TYPES

postulate BType : Set -- set of base types

postulate dec-bty : (B B' : BType) → Dec (B ≡ B')

GType = BType


-- VALUE AND COMPUTATION TYPES

mutual

  data VType : Set where
    ``  : GType → VType
    _⇒_ : VType → CType → VType
    ⟨_⟩ : VType → VType

  data CType : Set where
    _!_ : VType → O × I → CType

infix 30 _⇒_
infix 30 _!_
