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
            {op : Σₙ}
            {p : op ∈ₒ o}
            {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ ``(arₙ op)}
            {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X ! (o , i)} →
            Result⟨ Γ ∣ M ⟩ →
            -------------------------------
            Result⟨ Γ ∣ ↑ op p V M ⟩

  promise : {X Y : VType}
            {o o' : O}
            {i i' : I}
            {op : Σₙ}
            {p : lkpᵢ op i ≡ just (o' , i')}
            {M : ⟨⟨ Γ ⟩⟩ ∷ ``(arₙ op) ⊢M⦂ X ! (o' , i')}
            {N : ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)} →
            Result⟨ Γ ∷ X ∣ N ⟩ →
            -------------------------------------------
            Result⟨ Γ ∣ promise op ∣ p ↦ M `in N ⟩

  stuck   : {C : CType}
            {Y : VType}
            {y : ⟨ Y ⟩ ∈ ⟨⟨ Γ ⟩⟩}
            {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
            y ◄ M →
            --------------------------------
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
  inj₁ (let= M' `in N , context (let= [-] `in N) r)
... | inj₂ (return V) =
  inj₁ (N [ `_ [ V ]s ]m , let-return V N)
... | inj₂ (signal {X} {o} {i} {op} {p} {V} {M'} r) =
  inj₁ (↑ op p V (let= M' `in N) , let-↑ p V M' N)
... | inj₂ (promise {X} {Y} {o} {o'} {i} {i'} {op} {p} {M'} {M''} r) =
  inj₁ ((promise op ∣ p ↦ M' `in (let= M'' `in M-rename (comp-ren exchange wk₁) N)) , let-promise p M' M'' N)
... | inj₂ (stuck r) =
  inj₂ (stuck (let-in r))
progress ((` x) · W) with ⇒-not-in-ctx x
... | ()
progress (ƛ M · W) =
  inj₁ (M [ id-subst [ W ]s ]m , apply M W)
progress (↑ op p V M) with progress M
... | inj₁ (N , r) =
  inj₁ (↑ op p V N , (context (↑ op p V [-]) r))
... | inj₂ r =
  inj₂ (signal r)
progress (↓ op V M) with progress M
progress (↓ op V M) | inj₁ (N , r) =
  inj₁ (↓ op V N , context (↓ op V [-]) r)
... | inj₂ (return W) =
  inj₁ (return W , ↓-return V W)
... | inj₂ (signal {X} {o} {i} {op'} {p} {W'} {M'} q) =
  inj₁ (↑ op' (opₒ-in-↓ₑ op' p) W' (↓ op V M') , ↓-↑ p V W' M')
... | inj₂ (promise {X} {Y} {o} {o'} {i} {i'} {op'} {p} {M'} {M''} q) with decₙ op op'
... | yes refl =
  inj₁ (let= (subsume (⊑ₒ-↓ₑ-o' {o} p) (⊑ᵢ-↓ₑ-i' {o} p) (M' [ id-subst [ V ]s ]m)) `in
             ↓ op (V-rename wk₁ V) ((M-rename (comp-ren exchange wk₁) M'') [ id-subst [ ⟨ ` Hd ⟩ ]s ]m) ,
        ↓-promise-op p V M' M'')
... | no ¬r =
  inj₁ (promise_∣_↦_`in_ {o' = proj₁ (lkpᵢ-↓ₑ-neq {o = o} {i = i} ¬r p)}
                         {i' = proj₁ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} ¬r p))}
                         op'
                         (proj₁ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} ¬r p))))
                         (subsume (proj₁ (proj₂ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} ¬r p)))))
                                  (proj₂ (proj₂ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} ¬r p)))))
                                  M')
                         (↓ op (V-rename wk₁ V) M'') ,
        ↓-promise-op' ¬r p V M' M'')
progress (↓ op V M) | inj₂ (stuck r) =
  inj₂ (stuck (interrupt r))
progress (promise op ∣ p ↦ M `in N) with progress N
... | inj₁ (N' , r) =
  inj₁ (promise op ∣ p ↦ M `in N' , context (promise op ∣ p ↦ M `in [-]) r)
... | inj₂ r =
  inj₂ (promise r)
progress (await ` x until M) =
  inj₂ (stuck await)
progress (await ⟨ V ⟩ until M) =
  inj₁ (M [ `_ [ V ]s ]m , await-promise V M)
progress (subsume p q M) with progress M
... | inj₁ (N , r) =
  inj₁ (subsume p q N , context (subsume p q [-]) r)
... | inj₂ (return V) =
  inj₁ (return V , subsume-return V)
... | inj₂ (signal {X} {o} {i} {op} {r} {V} {M'} s) =
  inj₁ (↑ op (p op r) V (subsume p q M') , subsume-↑ r V M')
... | inj₂ (promise {X} {Y} {o} {o'} {i} {i'} {op} {r} {M'} {M''} s) =
  inj₁
    ((promise op ∣ lkpᵢ-next-eq q r ↦
      subsume (lkpᵢ-next-⊑ₒ q r) (lkpᵢ-next-⊑ᵢ q r) M' `in
      subsume p q M'')
     , subsume-promise r M' M'')
... | inj₂ (stuck r) =
  inj₂ (stuck (subsume r))


-- PROGRESS THEOREM FOR CLOSED COMPUTATIONS

closed-progress : {C : CType} →
                  (M : [] ⊢M⦂ C) →
                  --------------------------
                  (Σ[ N ∈ [] ⊢M⦂ C ] (M ↝ N)
                   ⊎
                   Result⟨ [] ∣ M ⟩)

closed-progress M =
  progress M
