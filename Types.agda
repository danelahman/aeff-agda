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


-- PROCESS TYPES

data PTypeShape : Set where
  _!_ : VType → I → PTypeShape
  _∥_ : PTypeShape → PTypeShape → PTypeShape

data PType : O → Set where

  _‼_,_ : (X : VType) →
          (o : O) →
          (i : I) →
          ---------------
          PType o
  
  _∥_   : {o o' : O} →
          (PP : PType o) →
          (QQ : PType o') →
          ---------------------------
          PType (o ∪ₒ o')


-- ACTION OF INTERRUPTS ON PROCESS TYPES

_↓ₚₚ_ : (op : Σₛ) → {o : O} →
        PType o → Σ[ o' ∈ O ] PType o'
op ↓ₚₚ (X ‼ o , i) with op ↓ₑ (o , i)
... | (o' , i') =
  o' , (X ‼ o' , i')
op ↓ₚₚ (PP ∥ QQ) with op ↓ₚₚ PP | op ↓ₚₚ QQ
... | (o'' , PP') | (o''' , QQ') =
  (o'' ∪ₒ o''') , (PP' ∥ QQ')


_↓ₚ_ : (op : Σₛ) → {o : O} →
       (PP : PType o) → PType (proj₁ (op ↓ₚₚ PP))

op ↓ₚ PP = proj₂ (op ↓ₚₚ PP)


-- ACTION OF INTERRUPTS ON PROCESS TYPES PRESERVES SIGNAL ANNOTATIONS

{- LEMMA 4.1 -}

↓ₚ-⊑ₒ : {op : Σₛ}
        {o : O} →
        (PP : PType o) →
        ----------------------
        o ⊑ₒ proj₁ (op ↓ₚₚ PP)

↓ₚ-⊑ₒ (X ‼ o , i) =
  ↓ₑ-⊑ₒ
↓ₚ-⊑ₒ (PP ∥ QQ) =
  ∪ₒ-fun (↓ₚ-⊑ₒ PP) (↓ₚ-⊑ₒ QQ)
