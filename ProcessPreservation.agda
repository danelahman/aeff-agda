open import Data.List hiding ([_]) renaming (_∷_ to _::_)
open import Data.Maybe
open import Data.Product

open import Calculus
open import EffectAnnotations
open import Preservation
open import ProcessCalculus
open import ProcessTypes
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module ProcessPreservation where

-- WELL-TYPED SIGNAL HOISTING CONTEXTS

data _⊢H[_]⦂_ (Γ : Ctx) : (Δ : BCtx) → CType → Set where

  [-]              : {C : CType} →
                     -------------
                     Γ ⊢H[ [] ]⦂ C

  promise_∣_↦_`in_ : {Δ : BCtx}
                     {X Y : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (op : Σᵢ) →
                     lkpᵢ op i ≡ just (o' , i') →
                     Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i') →
                     Γ ∷ ⟨ X ⟩ ⊢H[ Δ ]⦂ Y ! (o , i) →
                     ----------------------------------
                     Γ ⊢H[ X :: Δ ]⦂ Y ! (o , i)

  subsume          : {Δ : BCtx}
                     {X : VType}
                     {o o' : O}
                     {i i' : I} →
                     o ⊑ₒ o' →
                     i ⊑ᵢ i' → 
                     Γ ⊢H[ Δ ]⦂ X ! (o , i) →
                     ------------------------
                     Γ ⊢H[ Δ ]⦂ X ! (o' , i')


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED SIGNAL HOISTING CONTEXT

hole-ty-s : {Γ : Ctx} {Δ : BCtx} {C : CType} → Γ ⊢H[ Δ ]⦂ C → CType
hole-ty-s {_} {_} {C} [-] =
  C
hole-ty-s (promise op ∣ p ↦ M `in H) =
  hole-ty-s H
hole-ty-s (subsume p q H) =
  hole-ty-s H


-- FILLING A WELL-TYPED SIGNAL HOISTING CONTEXT

infix 30 _[_]h

_[_]h : {Γ : Ctx} {Δ : BCtx} {C : CType} → (H : Γ ⊢H[ Δ ]⦂ C) → Γ ⋈ Δ ⊢M⦂ (hole-ty-s H) → Γ ⊢M⦂ C
[-] [ M ]h =
  M
(promise op ∣ p ↦ N `in E) [ M ]h =
  promise op ∣ p ↦ N `in (E [ M ]h)
subsume p q E [ M ]h =
  subsume p q (E [ M ]h)


-- EVOLUTION OF PROCESS TYPES

infix 10 _⇝_

data _⇝_ : PType → PType → Set where

  id  : {PP : PType} →
        -------------------
        PP ⇝ PP

  op  : {X : VType}
        {o o' : O}
        {i i' : I} → 
        (op : Σᵢ) →
        op ↓ₑ (o , i) ≡ (o' , i') →
        ---------------------------
        (X ! i) ‼ o ⇝ (X ! i') ‼ o'

  par : {PP PP' QQ QQ' : SkelPType}
        {o o' o'' o''' : O} → 
        PP ‼ o ⇝ PP' ‼ o' →
        QQ ‼ o ⇝ QQ' ‼ o'' →
        o' ⊑ₒ o''' →
        o'' ⊑ₒ o''' →
        ---------------------------------
        (PP ∥ QQ) ‼ o ⇝ (PP' ∥ QQ') ‼ o''' 

  
-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED PROCESSES
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

infix 10 _[_]↝_

data _[_]↝_ {Γ : Ctx} : {PP : PType} → Γ ⊢P⦂ PP → {QQ : PType} → PP ⇝ QQ → Γ ⊢P⦂ PP → Set where

  run : {X : VType}
        {o : O}
        {i : I}
        {M N : Γ ⊢M⦂ X ! (o , i)} → 
        M ↝ N →
        ---------------------------
        (run M) [ id ]↝ (run N)

  -- ...

