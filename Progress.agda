open import Data.Empty
open import Data.List hiding ([_]) renaming (_∷_ to _::_)
open import Data.Maybe
open import Data.Product
open import Data.Sum

open import Calculus
open import EffectAnnotations
open import Preservation
open import Renamings
open import Substitutions
open import StuckComputations
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module Progress where

-- WRAPPING PROMISES AROUND A CONTEXT

⟨⟨_⟩⟩ : Ctx → Ctx
⟨⟨ [] ⟩⟩ = []
⟨⟨ Δ ∷ X ⟩⟩ = ⟨⟨ Δ ⟩⟩ ∷ ⟨ X ⟩


-- RESULTS

data Result⟨_∣_⟩ (Δ : Ctx) : {C : CType} → ⟨⟨ Δ ⟩⟩ ⊢M⦂ C → Set where

  return  : {X : VType}
            {o : O}
            {i : I}
            (V : ⟨⟨ Δ ⟩⟩ ⊢V⦂ X) →
            --------------------------------------
            Result⟨ Δ ∣ return {o = o} {i = i} V ⟩

  signal  : {X : VType}
            {o : O}
            {i : I}
            {op : Σₒ}
            {p : op ∈ₒ o}
            {V : ⟨⟨ Δ ⟩⟩ ⊢V⦂ ``(arₒ op)}
            {M : ⟨⟨ Δ ⟩⟩ ⊢M⦂ X ! (o , i)} →
            Result⟨ Δ ∣ M ⟩ →
            -------------------------------
            Result⟨ Δ ∣ ↑ op p V M ⟩

  promise : {X Y : VType}
            {o o' : O}
            {i i' : I}
            {op : Σᵢ}
            {p : lkpᵢ op i ≡ just (o' , i')}
            {M : ⟨⟨ Δ ⟩⟩ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i')}
            {N : ⟨⟨ Δ ⟩⟩ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)} →
            (Result⟨ Δ ∷ X ∣ N ⟩
             ⊎
             (Hd ◅ N)) →
            ----------------------------------------------
            Result⟨ Δ ∣ promise op ∣ p ↦ M `in N ⟩
 
  subsume : {X : VType}
            {o o' : O}
            {i i' : I}
            {p : o ⊑ₒ o'}
            {q : i ⊑ᵢ i'}
            {M : ⟨⟨ Δ ⟩⟩ ⊢M⦂ X ! (o , i)} → 
            Result⟨ Δ ∣ M ⟩ →
            -------------------------------
            Result⟨ Δ ∣ subsume p q M ⟩

