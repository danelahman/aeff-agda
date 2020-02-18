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
    
data _◄_ {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) : {C : CType} → Γ ⊢M⦂ C → Set where

  await     : {C : CType}
              {M : Γ ∷ X ⊢M⦂ C} →
              -------------------------
              x ◄ (await (` x) until M)

  let-in    : {X Y : VType}
              {o : O}
              {i : I}
              {M : Γ ⊢M⦂ X ! (o , i)}
              {N : Γ ∷ X ⊢M⦂ Y ! (o , i)} →
              x ◄ M →
              -----------------------------
              x ◄ (let= M `in N)

  interrupt : {X : VType}
              {o : O}
              {i : I}
              {op : Σₙ}
              {V : Γ ⊢V⦂ ``(arₙ op)}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ◄ M →
              -------------------------
              x ◄ (↓ op V M)

  subsume   : {X : VType}
              {o o' : O}
              {i i' : I}
              {p : o ⊑ₒ o'}
              {q : i ⊑ᵢ i'}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ◄ M →
              -------------------------
              x ◄ (subsume p q M)


-- DECIDING IF A COMPUTATION IS TEMPORARILY STUCK DUE TO AWAITING FOR A PARTICULAR PROMISE

dec◄ : {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) → {C : CType} → (M : Γ ⊢M⦂ C) → Dec (x ◄ M)
dec◄ x (return V) =
  no (λ ())
dec◄ {Γ} {X} x (let= M `in N) with dec◄ x M
... | yes p =
  yes (let-in p)
... | no ¬p =
  no (λ { (let-in q) → contradiction q ¬p })
dec◄ x (letrec M `in N) =
  no (λ ())
dec◄ x (V · W) =
  no (λ ())
dec◄ x (↑ op p V M) =
  no (λ ())
dec◄ {Γ} {X} x (↓ op V M) with dec◄ x M
... | yes p =
  yes (interrupt p)
... | no ¬p =
  no (λ { (interrupt q) → contradiction q ¬p })
dec◄ x (promise op ∣ p ↦ M `in N) =
  no (λ ())
dec◄ {Γ} {X} x (await_until_ {Y} (` y) M) with dec-vty X Y
dec◄ {Γ} {.Y} x (await_until_ {Y} (` y) M) | yes refl with dec-var x y
... | yes refl =
  yes await
... | no ¬p =
  no (λ { await → contradiction refl ¬p })
dec◄ {Γ} {X} x (await_until_ {Y} (` y) M) | no ¬p =
  no (λ { await → contradiction refl ¬p })  
dec◄ x (await ⟨ V ⟩ until M) =
  no (λ ())
dec◄ {Γ} {X} x (subsume p q M) with dec◄ x M
... | yes r =
  yes (subsume r)
... | no ¬r =
  no (λ { (subsume s) → contradiction s ¬r })
