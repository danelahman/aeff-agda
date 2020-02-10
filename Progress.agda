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

module Progress where


-- COMPUTATIONS THAT ARE STUCK ON WAITING FOR A PARTICULAR PROMISE
    
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
              {op : Σᵢ}
              {V : Γ ⊢V⦂ ``(arᵢ op)}
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

data _◅_ {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) : {C : CType} → Γ ⊢M⦂ C → Set where

  ◅◄        : {C : CType}
              {M : Γ ⊢M⦂ C} →
              x ◄ M →
              ---------------
              x ◅ M

  signal    : {X : VType}
              {o : O}
              {i : I}
              {op : Σₒ}
              {p : op ∈ₒ o}
              {V : Γ ⊢V⦂ ``(arₒ op)}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ◅ M →
              -------------------------
              x ◅ (↑ op p V M)

  promise   : {X Y : VType}
              {o o' : O}
              {i i' : I} 
              {op : Σᵢ}
              {p : lkpᵢ op i ≡ just (o' , i')}
              {M : Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i')}
              {N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)} →
              Tl x ◅ N →
              ----------------------------------
              x ◅ (promise op ∣ p ↦ M `in N)

  subsume   : {X : VType}
              {o o' : O}
              {i i' : I}
              {p : o ⊑ₒ o'}
              {q : i ⊑ᵢ i'}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ◅ M →
              -------------------------
              x ◅ (subsume p q M)


-- DECIDING IF A COMPUTATION IS STUCK ON WAITING FOR A PARTICULAR PROMISE

dec◄ : {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) → {C : CType} → (M : Γ ⊢M⦂ C) → Dec (x ◄ M)
dec◄ x (return V) =
  no (λ ())
dec◄ {Γ} {X} x (let= M `in N) with dec◄ x M
... | yes p =
  yes (let-in p)
... | no ¬p =
  no (λ q → contradiction (inj-let q) ¬p)

  where
    inj-let : {Y Z : VType} {o : O} {i : I} {M : Γ ⊢M⦂ Y ! (o , i)} {N : Γ ∷ Y ⊢M⦂ Z ! (o , i)} → x ◄ (let= M `in N) → x ◄ M
    inj-let (let-in r) = r

dec◄ x (V · W) =
  no (λ ())
dec◄ x (↑ op p V M) =
  no (λ ())
dec◄ {Γ} {X} x (↓ op V M) with dec◄ x M
... | yes p =
  yes (interrupt p)
... | no ¬p =
  no (λ q → contradiction (inj-interrupt q) ¬p)

  where
    inj-interrupt : {Y : VType} {o : O} {i : I} {op : Σᵢ} {V : Γ ⊢V⦂ ``(arᵢ op)} {M : Γ ⊢M⦂ Y ! (o , i)} → x ◄ ↓ op V M → x ◄ M
    inj-interrupt (interrupt r) = r

dec◄ x (promise op ∣ p ↦ M `in N) =
  no (λ ())
  
dec◄ x (await ` y until M) =
  {!!}
dec◄ x (await ⟨ V ⟩ until M) =
  no impossible-await

  where
    impossible-await : ¬ (x ◄ (await ⟨ V ⟩ until M))
    impossible-await ()

dec◄ {Γ} {X} x (subsume p q M) with dec◄ x M
... | yes r =
  yes (subsume r)
... | no ¬r =
  no (λ s → contradiction (inj-subsume s) ¬r)

  where
    inj-subsume : {Y : VType} {o o' : O} {i i' : I} {p : o ⊑ₒ o'} {q : i ⊑ᵢ i'} {M : Γ ⊢M⦂ Y ! (o , i)} → x ◄ subsume p q M → x ◄ M
    inj-subsume (subsume r) = r


dec◅ : {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) → {C : CType} → (M : Γ ⊢M⦂ C) → Dec (x ◅ M)
dec◅ x M = {!!}



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
            (op : Σₒ) →
            (p : op ∈ₒ o) →
            (V : ⟨⟨ Δ ⟩⟩ ⊢V⦂ ``(arₒ op)) →
            (M : ⟨⟨ Δ ⟩⟩ ⊢M⦂ X ! (o , i)) →
            Result⟨ Δ ∣ M ⟩ →
            -------------------------------
            Result⟨ Δ ∣ ↑ op p V M ⟩

  promise : {X Y : VType}
            {o o' : O}
            {i i' : I}
            (op : Σᵢ) →
            (p : lkpᵢ op i ≡ just (o' , i')) →
            (M : ⟨⟨ Δ ⟩⟩ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i')) →
            (N : ⟨⟨ Δ ⟩⟩ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
            (Result⟨ Δ ∷ X ∣ N ⟩
             ⊎
             (Hd ◅ N)) →
            ----------------------------------------------
            Result⟨ Δ ∣ promise op ∣ p ↦ M `in N ⟩
 


