open import AEff
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

_[_]s : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]s) Hd = V
(s [ V ]s) (Tl x) = s x


-- LIFTING SUBSTITUTIONS

lift : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)


-- ACTION OF SUBSTITUTIONS ON WELL-TYPED TERMS

mutual

  infix 40 _[_]v
  infix 40 _[_]m

  _[_]v : {Γ Γ' : Ctx} → {X : VType} → Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X
  (` x) [ s ]v =
    s x
  (`` c) [ s ]v =
    `` c
  (ƛ M) [ s ]v =
    ƛ (M [ lift s ]m)
  ⟨ V ⟩ [ s ]v =
    ⟨ V [ s ]v ⟩

  _[_]m : {Γ Γ' : Ctx} → {C : CType} → Γ ⊢M⦂ C → Sub Γ Γ'  → Γ' ⊢M⦂ C
  (return V) [ s ]m =
    return (V [ s ]v)
  (let= M `in N) [ s ]m =
    let= (M [ s ]m) `in (N [ lift s ]m)
  (letrec M `in N) [ s ]m =
    letrec M [ lift (lift s) ]m `in (N [ lift s ]m)
  (V · W) [ s ]m =
    (V [ s ]v) · (W [ s ]v)
  (↑ op p V M) [ s ]m =
    ↑ op p (V [ s ]v) (M [ s ]m)
  (↓ op V M) [ s ]m =
    ↓ op (V [ s ]v) (M [ s ]m)
  (promise op ∣ p ↦ M `in N) [ s ]m =
    promise op ∣ p ↦ (M [ lift s ]m) `in (N [ lift s ]m)
  (await V until M) [ s ]m =
    await (V [ s ]v) until (M [ lift s ]m)
  (coerce p q M) [ s ]m =
    coerce p q (M [ s ]m)
