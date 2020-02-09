open import Calculus
open import EffectAnnotations
open import Renamings
open import Types hiding (``)

open import Relation.Binary.PropositionalEquality hiding ([_])

module Substitutions where

-- SET OF SUBSTITUTIONS BETWEEN CONTEXTS

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : VType} → X ∈ Γ → Γ' ⊢V⦂ X


-- IDENTITY AND EXTENSION SUBSTITUTIONS

id-subst : {Γ : Ctx} → Sub Γ Γ
id-subst x = ` x

_[_]ₛ : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]ₛ) Hd = V
(s [ V ]ₛ) (Tl x) = s x


-- LIFTING SUBSTITUTIONS

lift : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)


-- ACTION OF SUBSTITUTIONS ON WELL-TYPED TERMS

mutual

  infix 40 _[_]ᵥ
  infix 40 _[_]ₘ

  _[_]ᵥ : {Γ Γ' : Ctx} → {X : VType} → Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X
  (` x) [ s ]ᵥ =
    s x
  (`` c) [ s ]ᵥ =
    `` c
  (ƛ M) [ s ]ᵥ =
    ƛ (M [ lift s ]ₘ)
  ⟨ V ⟩ [ s ]ᵥ =
    ⟨ V [ s ]ᵥ ⟩

  _[_]ₘ : {Γ Γ' : Ctx} → {C : CType} → Γ ⊢M⦂ C → Sub Γ Γ'  → Γ' ⊢M⦂ C
  (return V) [ s ]ₘ =
    return (V [ s ]ᵥ)
  (let= M `in N) [ s ]ₘ =
    let= (M [ s ]ₘ) `in (N [ lift s ]ₘ)
  (V · W) [ s ]ₘ =
    (V [ s ]ᵥ) · (W [ s ]ᵥ)
  (↑ op p V M) [ s ]ₘ =
    ↑ op p (V [ s ]ᵥ) (M [ s ]ₘ)
  (↓ op V M) [ s ]ₘ =
    ↓ op (V [ s ]ᵥ) (M [ s ]ₘ)
  (promise op ∣ p ↦ M `in N) [ s ]ₘ =
    promise op ∣ p ↦ (M [ lift s ]ₘ) `in (N [ lift s ]ₘ)
  (await V until M) [ s ]ₘ =
    await (V [ s ]ᵥ) until (M [ lift s ]ₘ)
  (coerce p q M) [ s ]ₘ =
    coerce p q (M [ s ]ₘ)
