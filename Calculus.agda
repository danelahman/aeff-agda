open import Data.Maybe
open import Data.Product hiding (Σ)

open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Operations
open import Types

module Calculus where

postulate arₒ : Σₒ → GType -- arity assignment to outgoing signals
postulate arᵢ : Σᵢ → GType  -- arity assignment to incoming interrupts

postulate Σₖ : Set        -- set of ground constants
postulate arₖ : Σₖ → GType -- arity assignment to ground constants

infixl 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A

Ctx = SnocList VType

data _∈_ (X : VType) : Ctx → Set where
  Hd : {Γ : Ctx} → X ∈ (Γ ∷ X)
  Tl : {Γ : Ctx} {Y : VType} → X ∈ Γ → X ∈ (Γ ∷ Y)

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where
  
    `_  : {X : VType} →
          X ∈ Γ →
          -------------
          Γ ⊢V⦂ X
          
    ``_  : (c : Σₖ) →
          --------------
          Γ ⊢V⦂ ``(arₖ c)
          
    ƛ   : {X : VType}
          {C : CType} →
          Γ ∷ X ⊢M⦂ C → 
          -------------
          Γ ⊢V⦂ X ⇒ C

    ⟨_⟩ : {X : VType} →
          Γ ⊢V⦂ X →
          -------------
          Γ ⊢V⦂ ⟨ X ⟩
          

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

    _·_              : {X : VType}
                       {C : CType} → 
                       Γ ⊢V⦂ X ⇒ C →
                       Γ ⊢V⦂ X →
                       -------------
                       Γ ⊢M⦂ C

    ↑                : {X : VType}
                       {o : O}
                       {i : I} →
                       (op : Σₒ) →
                       op ∈ₒ o →
                       Γ ⊢V⦂ ``(arₒ op) →
                       Γ ⊢M⦂ X ! (o , i) →
                       -------------------
                       Γ ⊢M⦂ X ! (o , i)

    ↓                : {X : VType}
                       {o : O}
                       {i : I}
                       (op : Σᵢ) →
                       Γ ⊢V⦂ ``(arᵢ op) →
                       Γ ⊢M⦂ X ! (o , i) →
                       ----------------------
                       Γ ⊢M⦂ X ! op ↓ₑ (o , i)

    promise_∣_↦_`in_ : {X Y : VType}
                       {o o' : O}
                       {i i' : I} → 
                       (op : Σᵢ) →
                       lkpᵢ op i ≡ just (o' , i') →
                       Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i') →
                       Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i) →
                       ----------------------------------
                       Γ ⊢M⦂ Y ! (o , i)

    await_until_     : {X : VType}
                       {C : CType} → 
                       Γ ⊢V⦂ ⟨ X ⟩ →
                       Γ ∷ X ⊢M⦂ C →
                       --------------
                       Γ ⊢M⦂ C

    coerce           : {X : VType}
                       {o o' : O}
                       {i i' : I} →
                       o ⊑ₒ o' →
                       i ⊑ᵢ i' → 
                       Γ ⊢M⦂ X ! (o , i) →
                       -------------------
                       Γ ⊢M⦂ X ! (o' , i')
                       
                        
infix 40 _·_