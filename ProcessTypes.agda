open import Data.List
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality)
open import Relation.Nullary
open import Relation.Nullary.Negation

open import EffectAnnotations
open import Types

module ProcessTypes where

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

_↓ₚₚ_ : (op : Σₙ) → {o : O} →
        PType o → Σ[ o' ∈ O ] PType o'
op ↓ₚₚ (X ‼ o , i) with op ↓ₑ (o , i)
... | (o' , i') =
  o' , (X ‼ o' , i')
op ↓ₚₚ (PP ∥ QQ) with op ↓ₚₚ PP | op ↓ₚₚ QQ
... | (o'' , PP') | (o''' , QQ') =
  (o'' ∪ₒ o''') , (PP' ∥ QQ')


_↓ₚ_ : (op : Σₙ) → {o : O} →
       (PP : PType o) → PType (proj₁ (op ↓ₚₚ PP))

op ↓ₚ PP = proj₂ (op ↓ₚₚ PP)


-- ACTION OF INTERRUPTS ON PROCESS TYPES PRESERVES SIGNAL ANNOTATIONS

↓ₚ-⊑ₒ : {op : Σₙ}
        {o : O} →
        (PP : PType o) →
        ----------------------
        o ⊑ₒ proj₁ (op ↓ₚₚ PP)

↓ₚ-⊑ₒ (X ‼ o , i) =
  ↓ₑ-⊑ₒ
↓ₚ-⊑ₒ (PP ∥ QQ) =
  ∪ₒ-fun (↓ₚ-⊑ₒ PP) (↓ₚ-⊑ₒ QQ)






{-
-- SUBTYPING RELATIONS ON PROCESS TYPES

infix 10 _⊑ₚ_

data _⊑ₚ_ : PTypeShape → PTypeShape → Set where

  sub-run : {X : VType}
            {i i' : I} →
            i ⊑ᵢ i' →
            ----------------
            X ! i ⊑ₚ X ! i'

  sub-par : {PP PP' QQ QQ' : PTypeShape} → 
            PP ⊑ₚ PP' →
            QQ ⊑ₚ QQ' →
            --------------------
            PP ∥ QQ ⊑ₚ PP' ∥ QQ'


-- SUBTYPING RELATION FOR PROCESS TYPES IS A PREORDER

⊑ₚ-refl : {PP : PTypeShape} →
          ------------------
          PP ⊑ₚ PP

⊑ₚ-refl {X ! i} =
  sub-run ⊑ᵢ-refl
⊑ₚ-refl {PP ∥ QQ} =
  sub-par ⊑ₚ-refl ⊑ₚ-refl 


⊑ₚ-trans : {PP QQ RR : PTypeShape} →
           PP ⊑ₚ QQ →
           QQ ⊑ₚ RR → 
           ------------------------
           PP ⊑ₚ RR

⊑ₚ-trans (sub-run p) (sub-run q) =
  sub-run (⊑ᵢ-trans p q)
⊑ₚ-trans (sub-par p q) (sub-par r s) =
  sub-par (⊑ₚ-trans p r) (⊑ₚ-trans q s)


-- ACTION OF INTERRUPTS ON PROCESS TYPES

_↓ₚ_ : (op : Σₙ) → PTypeShape × O → PTypeShape × O
op ↓ₚ ((X ! i) , o) with op ↓ₑ (o , i)
... | (o' , i') =
  (X ! i') , o'
op ↓ₚ ((PP ∥ QQ) , o) with op ↓ₚ (PP , o) | op ↓ₚ (QQ , o)
... | (PP' , o') | (QQ' , o'') =
  (PP' ∥ QQ') , (o' ∪ₒ o'')


-- SIGNAL ANNOTATIONS ARE PRESERVED BY THE ACTION OF INTERRUPTS ON PROCESS TYPES

↓ₚ-⊑ₒ :  (PP : PTypeShape) →
         {o : O}
         {op : Σₙ} →
         ---------------------------
         o ⊑ₒ proj₂ (op ↓ₚ (PP , o))

↓ₚ-⊑ₒ (X ! i) {o} {op} op' p =
  ↓ₑ-⊑ₒ op' p
↓ₚ-⊑ₒ (PP ∥ QQ) {o} {op} op' p with ↓ₚ-⊑ₒ PP {o} {op} op' p
... | r =
  ∪ₒ-inl op' r


-- ACTION OF INTERRUPTS ON PROCESS TYPES IS MONOTONIC

↓ₚ-monotonicₚ : {PP QQ : PTypeShape}
                {o o' : O}
                {op : Σₙ} → 
                PP ⊑ₚ QQ →
                o ⊑ₒ o' →
                -------------------------------------------------
                proj₁ (op ↓ₚ (PP , o)) ⊑ₚ proj₁ (op ↓ₚ (QQ , o'))

↓ₚ-monotonicₚ (sub-run p) q =
  sub-run (↓ₑ-monotonicᵢ q p)
↓ₚ-monotonicₚ (sub-par p q) r =
  sub-par (↓ₚ-monotonicₚ p r) (↓ₚ-monotonicₚ q r)
               

↓ₚ-monotonicₒ : {PP QQ : PTypeShape}
                {o o' : O}
                {op : Σₙ} → 
                PP ⊑ₚ QQ →
                o ⊑ₒ o' →
                -------------------------------------------------
                proj₂ (op ↓ₚ (PP , o)) ⊑ₒ proj₂ (op ↓ₚ (QQ , o'))

↓ₚ-monotonicₒ (sub-run p) q =
  ↓ₑ-monotonicₒ q p
↓ₚ-monotonicₒ {_} {_} {_} {_} {op} (sub-par p q) r =
  ∪ₒ-copair (⊑ₒ-trans (↓ₚ-monotonicₒ p r) ∪ₒ-inl)
            (⊑ₒ-trans (↓ₚ-monotonicₒ q r) ∪ₒ-inr)

-}
