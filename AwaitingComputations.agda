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
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module AwaitingComputations where

-- COMPUTATIONS THAT ARE TEMPORARILY STUCK DUE TO AWAITING FOR A PARTICULAR PROMISE
    
data _⧗_ {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) : {C : CType} → Γ ⊢M⦂ C → Set where

  await     : {C : CType}
              {M : Γ ∷ X ⊢M⦂ C} →
              -------------------------
              x ⧗ (await (` x) until M)

  let-in    : {X Y : VType}
              {o : O}
              {i : I}
              {M : Γ ⊢M⦂ X ! (o , i)}
              {N : Γ ∷ X ⊢M⦂ Y ! (o , i)} →
              x ⧗ M →
              -----------------------------
              x ⧗ (let= M `in N)

  interrupt : {X : VType}
              {o : O}
              {i : I}
              {op : Σₛ}
              {V : Γ ⊢V⦂ ``(payload op)}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ⧗ M →
              -------------------------
              x ⧗ (↓ op V M)

  subsume   : {X : VType}
              {o o' : O}
              {i i' : I}
              {p : o ⊑ₒ o'}
              {q : i ⊑ᵢ i'}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ⧗ M →
              -------------------------
              x ⧗ (subsume p q M)
