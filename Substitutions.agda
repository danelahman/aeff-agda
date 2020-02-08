open import Calculus
open import Operations
open import Renamings
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])

module Substitutions where

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : VType} → X ∈ Γ → Γ' ⊢V⦂ X

lift : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)

mutual

  V-subst : {Γ Γ' : Ctx}  → Sub Γ Γ'  → {X : VType}  → Γ ⊢V⦂ X  → Γ' ⊢V⦂ X
  V-subst s (` x) =
    s x
  V-subst s (`` c) =
    `` c
  V-subst s (ƛ M) =
    ƛ (M-subst (lift s) M)
  V-subst s ⟨ V ⟩ =
    ⟨ V-subst s V ⟩

  M-subst : {Γ Γ' : Ctx}  → Sub Γ Γ'  → {C : CType}  → Γ ⊢M⦂ C  → Γ' ⊢M⦂ C
  M-subst s (return V) =
    return (V-subst s V)
  M-subst s (let= M `in N) =
    let= M-subst s M `in M-subst (lift s) N
  M-subst s (V · W) =
    V-subst s V · V-subst s W
  M-subst s (↑ op p V M) =
    ↑ op p (V-subst s V) (M-subst s M)
  M-subst s (↓ op V M) =
    ↓ op (V-subst s V) (M-subst s M)
  M-subst s (promise op ∣ p ↦ M `in N) =
    promise op ∣ p ↦ M-subst (lift s) M `in M-subst (lift s) N
  M-subst s (await V until M) =
    await V-subst s V until M-subst (lift s) M

