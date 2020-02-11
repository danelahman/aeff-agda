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

infix 10 _⊑-sp_
infix 10 _⊑-p_

data _⊑-sp_ : SkelPType → SkelPType → Set where

  sub-run : {X : VType}
            {i i' : I} →
            i ⊑ᵢ i' →
            -----------------
            X ! i ⊑-sp X ! i'

  sub-par : {PP PP' QQ QQ' : SkelPType} → 
            PP ⊑-sp PP' →
            QQ ⊑-sp QQ' →
            ---------------------
            PP ∥ QQ ⊑-sp PP' ∥ QQ'

data _⊑-p_ : PType → PType → Set where

  sub-proc : {PP QQ : SkelPType}
             {o o' : O} → 
             PP ⊑-sp QQ →
             o ⊑ₒ o' →
             -------------------
             PP ‼ o ⊑-p QQ ‼ o'


-- ACTION OF INTERRUPTS ON PROCESS TYPES

_↓-p_ : (op : Σᵢ) → PType → PType
op ↓-p ((X ! i) ‼ o) with op ↓ₑ (o , i)
... | (o' , i') =
  (X ! i') ‼ o'
op ↓-p ((PP ∥ QQ) ‼ o) with op ↓-p (PP ‼ o) | op ↓-p (QQ ‼ o)
... | (PP' ‼ o') | (QQ' ‼ o'') =
  (PP' ∥ QQ') ‼ (o' ∪ₒ o'')
