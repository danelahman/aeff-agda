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
open import AwaitingComputations
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

  return   : {X : VType}
             {o : O}
             {i : I}
             (V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X) →
             --------------------------------------
             Result⟨ Γ ∣ return {o = o} {i = i} V ⟩

  signal   : {X : VType}
             {o : O}
             {i : I}
             {op : Σₛ}
             {p : op ∈ₒ o}
             {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ ``(payload op)}
             {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X ! (o , i)} →
             Result⟨ Γ ∣ M ⟩ →
             --------------------------------
             Result⟨ Γ ∣ ↑ op p V M ⟩

  promise  : {X Y : VType}
             {o o' : O}
             {i i' : I}
             {op : Σₛ}
             {p : lkpᵢ op i ≡ just (o' , i')}
             {M : ⟨⟨ Γ ⟩⟩ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i')}
             {N : ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)} →
             Result⟨ Γ ∷ X ∣ N ⟩ →
             ----------------------------------------------------
             Result⟨ Γ ∣ promise op ∣ p ↦ M `in N ⟩

  awaiting : {C : CType}
             {Y : VType}
             {y : ⟨ Y ⟩ ∈ ⟨⟨ Γ ⟩⟩}
             {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
             y ⧗ M →
             ---------------------
             Result⟨ Γ ∣ M ⟩


-- PROGRESS THEOREM FOR PROMISE-OPEN COMPUTATIONS

⇒-not-in-ctx : {Γ : Ctx} {X : VType} {C : CType} → X ⇒ C ∈ ⟨⟨ Γ ⟩⟩ → ⊥
⇒-not-in-ctx {Γ ∷ y} (Tl x) =
  ⇒-not-in-ctx x
  

progress : {Γ : Ctx} {C : CType} →
           (M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C) →
           -------------------------------
           (Σ[ N ∈ ⟨⟨ Γ ⟩⟩ ⊢M⦂ C ] (M ↝ N)
            ⊎
            Result⟨ Γ ∣ M ⟩)

progress (return V) =
  inj₂ (return V)
progress (let= M `in N) with progress M
... | inj₁ (M' , r) =
  inj₁ (_ , context (let= [-] `in N) r)
... | inj₂ (return V) =
  inj₁ (_ , let-return V N)
... | inj₂ (signal {_} {_} {_} {_} {p} {V} {M'} r) =
  inj₁ (_ , let-↑ p V M' N)
... | inj₂ (promise {_} {_} {_} {_} {_} {_} {_} {p} {M'} {M''} r) =
  inj₁ (_ , let-promise p M' M'' N)
... | inj₂ (awaiting R) =
  inj₂ (awaiting (let-in R))
progress (letrec M `in N) =
  inj₁ (_ , letrec-unfold M N)
progress ((` x) · W) with ⇒-not-in-ctx x
... | ()
progress (ƛ M · W) =
  inj₁ (M [ id-subst [ W ]s ]m , apply M W)
progress (↑ op p V M) with progress M
... | inj₁ (N , r) =
  inj₁ (_ , (context (↑ op p V [-]) r))
... | inj₂ r =
  inj₂ (signal r)
progress (↓ op V M) with progress M
progress (↓ op V M) | inj₁ (N , r) =
  inj₁ (_ , context (↓ op V [-]) r)
... | inj₂ (return W) =
  inj₁ (_ , ↓-return V W)
... | inj₂ (signal {X} {o} {i} {op'} {p} {W'} {M'} q) =
  inj₁ (_ , ↓-↑ p V W' M')
... | inj₂ (promise {_} {_} {_} {_} {_} {_} {op'} {p} {M'} {M''} q) with decₛ op op'
... | yes refl =
  inj₁ (_ , ↓-promise-op p V M' M'')
... | no ¬r =
  inj₁ (_ , ↓-promise-op' ¬r p V M' M'')
progress (↓ op V M) | inj₂ (awaiting r) =
  inj₂ (awaiting (interrupt r))
progress (promise op ∣ p ↦ M `in N) with progress N
... | inj₁ (N' , r) =
  inj₁ (_ , context (promise op ∣ p ↦ M `in [-]) r)
... | inj₂ r =
  inj₂ (promise r)
progress (await ` x until M) =
  inj₂ (awaiting await)
progress (await ⟨ V ⟩ until M) =
  inj₁ (_ , await-promise V M)
progress (coerce p q M) with progress M
... | inj₁ (N , r) =
  inj₁ (_ , context (coerce p q [-]) r)
... | inj₂ (return V) =
  inj₁ (_ , coerce-return V)
... | inj₂ (signal {X} {o} {i} {op} {r} {V} {M'} s) =
  inj₁ (_ , coerce-↑ r V M')
... | inj₂ (promise {_} {_} {_} {_} {_} {_} {_} {r} {M'} {M''} s) =
  inj₁ (_ , coerce-promise r M' M'')
... | inj₂ (awaiting R) =
  inj₂ (awaiting (coerce R))


-- PROGRESS THEOREM FOR CLOSED COMPUTATIONS

closed-progress : {C : CType} →
                  (M : [] ⊢M⦂ C) →
                  --------------------------
                  (Σ[ N ∈ [] ⊢M⦂ C ] (M ↝ N)
                   ⊎
                   Result⟨ [] ∣ M ⟩)

closed-progress M =
  progress M
