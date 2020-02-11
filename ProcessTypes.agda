open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality)
open import Relation.Nullary
open import Relation.Nullary.Negation

open import EffectAnnotations
open import Types

module ProcessTypes where

-- PROCESS TYPES

data SkelPType : Set where
  _!_ : VType → I → SkelPType
  _∥_ : SkelPType → SkelPType → SkelPType

data PType : Set where
  _‼_ : SkelPType → O → PType


-- SUBTYPING RELATIONS ON PROCESS TYPES

infix 10 _⊑ₚ_

data _⊑ₚ_ : SkelPType → SkelPType → Set where

  sub-run : {X : VType}
            {i i' : I} →
            i ⊑ᵢ i' →
            ----------------
            X ! i ⊑ₚ X ! i'

  sub-par : {PP PP' QQ QQ' : SkelPType} → 
            PP ⊑ₚ PP' →
            QQ ⊑ₚ QQ' →
            --------------------
            PP ∥ QQ ⊑ₚ PP' ∥ QQ'


-- SUBTYPING RELATION FOR PROCESS TYPES IS A PREORDER

⊑ₚ-refl : {PP : SkelPType} →
          ------------------
          PP ⊑ₚ PP

⊑ₚ-refl {X ! i} =
  sub-run ⊑ᵢ-refl
⊑ₚ-refl {PP ∥ QQ} =
  sub-par ⊑ₚ-refl ⊑ₚ-refl 


⊑ₚ-trans : {PP QQ RR : SkelPType} →
           PP ⊑ₚ QQ →
           QQ ⊑ₚ RR → 
           ------------------------
           PP ⊑ₚ RR

⊑ₚ-trans (sub-run p) (sub-run q) =
  sub-run (⊑ᵢ-trans p q)
⊑ₚ-trans (sub-par p q) (sub-par r s) =
  sub-par (⊑ₚ-trans p r) (⊑ₚ-trans q s)


-- ACTION OF INTERRUPTS ON PROCESS TYPES

_↓ₚ_ : (op : Σₙ) → SkelPType × O → SkelPType × O
op ↓ₚ ((X ! i) , o) with op ↓ₑ (o , i)
... | (o' , i') =
  (X ! i') , o'
op ↓ₚ ((PP ∥ QQ) , o) with op ↓ₚ (PP , o) | op ↓ₚ (QQ , o)
... | (PP' , o') | (QQ' , o'') =
  (PP' ∥ QQ') , (o' ∪ₒ o'')


-- SIGNAL ANNOTATIONS ARE PRESERVED BY THE ACTION

↓ₚ-in-lem :  (PP : SkelPType) →
             {o : O}
             {op op' : Σₙ} →
             op' ∈ₒ o →
             ----------------------------
             op' ∈ₒ proj₂ (op ↓ₚ (PP , o))
             
↓ₚ-in-lem (X ! i) {o} {op} p =
  opₒ-in-↓ₑ-lem p
↓ₚ-in-lem (PP ∥ QQ) {o} {op} {op'} p with ↓ₚ-in-lem PP {o} {op} {op'} p
... | r =
  ⊑ₒ-inl op' r
