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
                     (op : Σₙ) →
                     lkpᵢ op i ≡ just (o' , i') →
                     Γ ∷ ``(arₙ op) ⊢M⦂ X ! (o' , i') →
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


hole-ty-sₒ : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
             Γ ⊢H[ Δ ]⦂ X ! (o , i) → O
hole-ty-sₒ {_} {_} {_} {o} [-] =
  o
hole-ty-sₒ (promise op ∣ p ↦ M `in H) =
  hole-ty-sₒ H
hole-ty-sₒ (subsume p q H) =
  hole-ty-sₒ H


hole-ty-sᵢ : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
             Γ ⊢H[ Δ ]⦂ X ! (o , i) → I
hole-ty-sᵢ {_} {_} {_} {_} {o} [-] =
  o
hole-ty-sᵢ (promise op ∣ p ↦ M `in H) =
  hole-ty-sᵢ H
hole-ty-sᵢ (subsume p q H) =
  hole-ty-sᵢ H


hole-ty-⊑ₒ : {Γ : Ctx}
             {Δ : BCtx}
             {X : VType}
             {o : O}
             {i : I} →
             (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) →
             ------------------------------
             hole-ty-sₒ H ⊑ₒ o
hole-ty-⊑ₒ [-] =
  ⊑ₒ-refl
hole-ty-⊑ₒ (promise op ∣ p ↦ M `in H) =
  hole-ty-⊑ₒ H
hole-ty-⊑ₒ (subsume p q H) =
  ⊑ₒ-trans (hole-ty-⊑ₒ H) p


hole-ty-⊑ᵢ : {Γ : Ctx}
             {Δ : BCtx}
             {X : VType}
             {o : O}
             {i : I} →
             (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) →
             ------------------------------
             hole-ty-sᵢ H ⊑ᵢ i
hole-ty-⊑ᵢ [-] =
  ⊑ᵢ-refl
hole-ty-⊑ᵢ (promise op ∣ p ↦ M `in H) =
  hole-ty-⊑ᵢ H
hole-ty-⊑ᵢ (subsume p q H) =
  ⊑ᵢ-trans (hole-ty-⊑ᵢ H) q


-- FILLING A WELL-TYPED SIGNAL HOISTING CONTEXT

infix 30 _[_]h

_[_]h : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
        (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) → Γ ⋈ Δ ⊢M⦂ (X ! (hole-ty-sₒ H , hole-ty-sᵢ H)) →
        Γ ⊢M⦂ X ! (o , i)
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

  ops : {PP : SkelPType}
        {o : O}
        (op : Σₙ) → 
        ----------------------------------------------
        PP ‼ o
        ⇝
        proj₁ (op ↓ₚ (PP , o)) ‼ proj₂ (op ↓ₚ (PP , o))

  par : {PP PP' QQ QQ' : SkelPType}
        {o o' o'' : O} → 
        PP ‼ o ⇝ PP' ‼ o' →
        QQ ‼ o ⇝ QQ' ‼ o'' →
        ----------------------------------------
        (PP ∥ QQ) ‼ o ⇝ (PP' ∥ QQ') ‼ (o' ∪ₒ o'') 


-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-var : {Γ : Ctx} → (Δ : BCtx) → {A : BType} → `` A ∈ Γ ⋈ Δ → `` A ∈ Γ
strengthen-var [] x = x
strengthen-var (y :: Δ) x with strengthen-var Δ x
... | Tl p = p


strengthen-val : {Γ : Ctx} {Δ : BCtx} {A : BType} → Γ ⋈ Δ ⊢V⦂ `` A → Γ ⊢V⦂ `` A
strengthen-val {_} {Δ} (` x) =
  ` strengthen-var Δ x
strengthen-val (``_ c) =
  ``_ c

  
-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED PROCESSES
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

infix 10 _[_]↝_

data _[_]↝_ {Γ : Ctx} : {PP : PType} → Γ ⊢P⦂ PP → {QQ : PType} → PP ⇝ QQ → Γ ⊢P⦂ QQ → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run   : {X : VType}
          {o : O}
          {i : I}
          {M N : Γ ⊢M⦂ X ! (o , i)} → 
          M ↝ N →
          ---------------------------
          (run M) [ id ]↝ (run N)

  -- BROADCAST RULES

  bcast-l : {PP QQ : SkelPType}
            {o : O}
            {op : Σₙ} → 
            (p : op ∈ₒ o) →
            (V : Γ ⊢V⦂ `` (arₙ op)) →
            (P : Γ ⊢P⦂ PP ‼ o) →
            (Q : Γ ⊢P⦂ QQ ‼ o) →
            ------------------------
            (↑ op p V P ∥ Q)
            [ par id (ops op) ]↝
            (↑ op (⊑ₒ-inl op p)
                  V
                  (subsume ⊑ₚ-refl ⊑ₒ-inl P
                   ∥
                   subsume ⊑ₚ-refl ⊑ₒ-inr (↓ op V Q)))

  bcast-r : {PP QQ : SkelPType}
            {o : O}
            {op : Σₙ} → 
            (p : op ∈ₒ o) →
            (V : Γ ⊢V⦂ `` (arₙ op)) →
            (P : Γ ⊢P⦂ PP ‼ o) →
            (Q : Γ ⊢P⦂ QQ ‼ o) →
            ------------------------
            (P ∥ ↑ op p V Q)
            [ par (ops op) id ]↝
            (↑ op (⊑ₒ-inr op p)
                  V
                  (subsume ⊑ₚ-refl ⊑ₒ-inl (↓ op V P)
                   ∥
                   subsume ⊑ₚ-refl ⊑ₒ-inr Q))

  -- INTERRUPT RULES

  -- ...

  -- HOISTING RULE

  hoist : {Δ : BCtx}
          {X : VType}
          {o o' : O}
          {i i' : I} → 
          (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) → 
          {op : Σₙ} → 
          (p : op ∈ₒ hole-ty-sₒ H) →
          (V : Γ ⋈ Δ ⊢V⦂ `` (arₙ op)) →
          (M : Γ ⋈ Δ ⊢M⦂ X ! (hole-ty-sₒ H , hole-ty-sᵢ H)) →
          -----------------------------------------------
          (run (H [ ↑ op p V M ]h))
          [ id ]↝
          (↑ op (hole-ty-⊑ₒ H op p) (strengthen-val {Δ = Δ} V) (run (H [ M ]h)))

  -- CONTEXT RULE

  -- ...

