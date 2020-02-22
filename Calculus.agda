open import Data.Maybe
open import Data.Product hiding (Σ)

open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

open import EffectAnnotations
open import Types

module Calculus where

-- ARITY ASSIGNMENT TO SIGNATURES OF SIGNALS, INTERRUPTS, AND BASE CONSTANTS

postulate payload : Σₛ → GType     -- payload type assignment for signal and interrupt names

postulate Σ-base : Set             -- set of base constants
postulate ar-base : Σ-base → BType -- arity assignment to base constants


-- SNOC LISTS FOR MODELLING CONTEXTS

infixl 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A


-- CONTEXTS AND VARIABLES IN THEM (I.E., DE BRUIJN INDICES)

Ctx = SnocList VType

data _∈_ (X : VType) : Ctx → Set where
  Hd : {Γ : Ctx} → X ∈ (Γ ∷ X)
  Tl : {Γ : Ctx} {Y : VType} → X ∈ Γ → X ∈ (Γ ∷ Y)


-- DERIVATIONS OF WELL-TYPED TERMS

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where
  
    `_  : {X : VType} →
          X ∈ Γ →
          -------------
          Γ ⊢V⦂ X
          
    ``_  : (c : Σ-base) →
          --------------
          Γ ⊢V⦂ ``(ar-base c)
          
    ƛ   : {X : VType}
          {C : CType} →
          Γ ∷ X ⊢M⦂ C → 
          -------------
          Γ ⊢V⦂ X ⇒ C

    ⟨_⟩ : {X : VType} →
          Γ ⊢V⦂ X →
          -------------
          Γ ⊢V⦂ ⟨ X ⟩
          
  infix 40 _·_

  data _⊢M⦂_ (Γ : Ctx) : CType → Set where

    return           : {X : VType}
                       {o : O}
                       {i : I} →
                       Γ ⊢V⦂ X →
                       -----------------
                       Γ ⊢M⦂ X ! (o , i)

    let=_`in_        : {X Y : VType}
                       {o : O}
                       {i : I} → 
                       Γ ⊢M⦂ X ! (o , i) →
                       Γ ∷ X ⊢M⦂ Y ! (o , i) →
                       -----------------------
                       Γ ⊢M⦂ Y ! (o , i)

    letrec_`in_      : {X : VType}
                       {C D : CType} →
                       Γ ∷ (X ⇒ C) ∷ X ⊢M⦂ C →
                       Γ ∷ (X ⇒ C) ⊢M⦂ D →
                       -----------------------
                       Γ ⊢M⦂ D

    _·_              : {X : VType}
                       {C : CType} → 
                       Γ ⊢V⦂ X ⇒ C →
                       Γ ⊢V⦂ X →
                       -------------
                       Γ ⊢M⦂ C

    ↑                : {X : VType}
                       {o : O}
                       {i : I} →
                       (op : Σₛ) →
                       op ∈ₒ o →
                       Γ ⊢V⦂ ``(payload op) →
                       Γ ⊢M⦂ X ! (o , i) →
                       ----------------------
                       Γ ⊢M⦂ X ! (o , i)

    ↓                : {X : VType}
                       {o : O}
                       {i : I}
                       (op : Σₛ) →
                       Γ ⊢V⦂ ``(payload op) →
                       Γ ⊢M⦂ X ! (o , i) →
                       ----------------------
                       Γ ⊢M⦂ X ! op ↓ₑ (o , i)

    promise_∣_↦_`in_ : {X Y : VType}
                       {o o' : O}
                       {i i' : I} → 
                       (op : Σₛ) →
                       lkpᵢ op i ≡ just (o' , i') →
                       Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i') →
                       Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i) →
                       ------------------------------------------
                       Γ ⊢M⦂ Y ! (o , i)

    await_until_     : {X : VType}
                       {C : CType} → 
                       Γ ⊢V⦂ ⟨ X ⟩ →
                       Γ ∷ X ⊢M⦂ C →
                       --------------
                       Γ ⊢M⦂ C

    subsume          : {X : VType}
                       {o o' : O}
                       {i i' : I} →
                       o ⊑ₒ o' →
                       i ⊑ᵢ i' → 
                       Γ ⊢M⦂ X ! (o , i) →
                       -------------------
                       Γ ⊢M⦂ X ! (o' , i')
                        
