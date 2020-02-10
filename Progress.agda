open import Data.Empty
open import Data.List hiding ([_]) renaming (_∷_ to _::_)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

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
⟨⟨ Γ ∷ X ⟩⟩ = ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩


-- RESULTS

data Result⟨_∣_⟩ (Γ : Ctx) : {C : CType} → ⟨⟨ Γ ⟩⟩ ⊢M⦂ C → Set where

  return  : {X : VType}
            {o : O}
            {i : I}
            (V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X) →
            --------------------------------------
            Result⟨ Γ ∣ return {o = o} {i = i} V ⟩

  signal  : {X : VType}
            {o : O}
            {i : I}
            {op : Σₒ}
            {p : op ∈ₒ o}
            {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ ``(arₒ op)}
            {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X ! (o , i)} →
            Result⟨ Γ ∣ M ⟩ →
            -------------------------------
            Result⟨ Γ ∣ ↑ op p V M ⟩

  promise : {X Y : VType}
            {o o' : O}
            {i i' : I}
            {op : Σᵢ}
            {p : lkpᵢ op i ≡ just (o' , i')}
            {M : ⟨⟨ Γ ⟩⟩ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i')}
            {N : ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)} →
            (Result⟨ Γ ∷ X ∣ N ⟩
             ⊎
             (Hd ◅ N)) →
            -------------------------------------------
            Result⟨ Γ ∣ promise op ∣ p ↦ M `in N ⟩
 
  subsume : {X : VType}
            {o o' : O}
            {i i' : I}
            {p : o ⊑ₒ o'}
            {q : i ⊑ᵢ i'}
            {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X ! (o , i)} → 
            Result⟨ Γ ∣ M ⟩ →
            -------------------------------
            Result⟨ Γ ∣ subsume p q M ⟩


-- PROGRESS THEOREM

⇒-not-in-ctx : {Γ : Ctx} {X : VType} {C : CType} → X ⇒ C ∈ ⟨⟨ Γ ⟩⟩ → ⊥
⇒-not-in-ctx {Γ ∷ y} (Tl x) =
  ⇒-not-in-ctx x


◅-to-let : {Γ : Ctx} {X Y Z : VType} {o : O} {i : I}
           {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ Y ! (o , i)} {N : ⟨⟨ Γ ⟩⟩ ∷ Y ⊢M⦂ Z ! (o , i)} {x : ⟨ X ⟩ ∈ ⟨⟨ Γ ⟩⟩} →
           x ◅ M → x ◅ (let= M `in N)
◅-to-let p = {!!}

progress : {Γ : Ctx} {C : CType} →
           (M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C) →
           ({Y : VType} → (y : ⟨ Y ⟩ ∈ ⟨⟨ Γ ⟩⟩) → ¬ (y ◅ M)) →
           (Σ[ N ∈ ⟨⟨ Γ ⟩⟩ ⊢M⦂ C ] (M ↝ N)
            ⊎
            Result⟨ Γ ∣ M ⟩)
progress (return V) H =
  inj₂ (return V)
progress (let= M `in N) H with progress M (λ y → contraposition {!!} (H y))
... | p = {!!}
progress ((` x) · W) H with ⇒-not-in-ctx x
... | ()
progress (ƛ x · W) H =
  inj₁ (x [ `_ [ W ]ₛ ]ₘ , apply x W)
progress (↑ op p V M) H with progress M (λ y → contraposition signal (H y))
... | inj₁ (N , r) =
  inj₁ (↑ op p V N , context (↑ op p V [-]) r)
... | inj₂ r =
  inj₂ (signal r)
progress (↓ op V M) H with progress M (λ y → contraposition {!!} (H y))
... | p = {!!}
progress (promise op ∣ p ↦ M `in N) H with dec◅ Hd N
... | yes q =
  inj₂ (promise (inj₂ q))
... | no ¬q with progress N λ { Hd     → ¬q ;
                                (Tl y) → contraposition promise (H y) }
... | inj₁ (N' , r) =
  inj₁ (promise op ∣ p ↦ M `in N' , context (promise op ∣ p ↦ M `in [-]) r)
... | inj₂ r =
  inj₂ (promise (inj₁ r))
progress (await ` x until M) H =
  contradiction (◅◄ await) (H x)
progress (await ⟨ V ⟩ until M) H =
  inj₁ (M [ id-subst [ V ]ₛ ]ₘ , await-promise V M)
progress (subsume p q M) H with progress M (λ y → contraposition subsume (H y))
... | inj₁ (N , r) =
  inj₁ (subsume p q N , context (subsume p q [-]) r)
... | inj₂ r =
  inj₂ (subsume r)

