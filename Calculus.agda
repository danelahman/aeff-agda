open import Data.Maybe
open import Data.Product hiding (Σ)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Operations
open import Types

module Calculus where

postulate arₒ : Σₒ → GType -- arity assignment to outgoing signals
postulate arᵢ : Σᵢ → GType  -- arity assignment to incoming interrupts

postulate Σ : Set        -- set of ground constants
postulate ar : Σ → GType -- arity assignment to ground constants

infix 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A

Context = SnocList VType

data _∈_ : VType → Context → Set where
  Hd : {Γ : Context} {X : VType} → X ∈ (Γ ∷ X)
  Tl : {Γ : Context} {X Y : VType} → X ∈ Γ → X ∈ (Γ ∷ Y)

mutual

  data _∣_⊢V⦂_ (Γ Δ : Context) : VType → Set where
  
    v_  : {X : VType} →
          X ∈ Γ →
          -------------
          Γ ∣ Δ ⊢V⦂ X
          
    p_  : {X : VType} →
          X ∈ Δ →
          ---------------
          Γ ∣ Δ ⊢V⦂ ⟨ X ⟩
          
    g_  : {A : GType} →
          (c : Σ) →
          -------------
          Γ ∣ Δ ⊢V⦂ G A
          
    ƛ   : {X : VType}
          {C : CType} →
          (Γ ∷ X) ∣ Δ ⊢M⦂ C → 
          -------------------
          Γ ∣ Δ ⊢V⦂ X ⇒ C

    ⟨_⟩ : {X : VType} →
          Γ ∣ Δ ⊢V⦂ X →
          ---------------
          Γ ∣ Δ ⊢V⦂ ⟨ X ⟩
          

  data _∣_⊢M⦂_ (Γ Δ : Context) : CType → Set where

    return            : {X : VType}
                        {o : O}
                        {i : I} →
                        Γ ∣ Δ ⊢V⦂ X →
                        ---------------------
                        Γ ∣ Δ ⊢M⦂ X ! (o , i)

    let=_`in_         : {X Y : VType}
                        {o : O}
                        {i : I} → 
                        Γ ∣ Δ ⊢M⦂ X ! (o , i) →
                        (Γ ∷ X) ∣ Δ ⊢M⦂ Y ! (o , i) →
                        -----------------------------
                        Γ ∣ Δ ⊢M⦂ Y ! (o , i)

    _·_               : {X : VType}
                        {C : CType} → 
                        Γ ∣ Δ ⊢V⦂ X ⇒ C →
                        Γ ∣ Δ ⊢V⦂ X →
                        -----------------
                        Γ ∣ Δ ⊢M⦂ C

    _↑                : {X : VType}
                        {o : O}
                        {i : I} →
                        (op : Σₒ) →
                        {_ : op ∈ₒ o} →
                        Γ ∣ Δ ⊢V⦂ G (arₒ op) →
                        Γ ∣ Δ ⊢M⦂ X ! (o , i) →
                        -----------------------
                        Γ ∣ Δ ⊢M⦂ X ! (o , i)

    _↓                : {X : VType}
                        {o : O}
                        {i : I}
                        (op : Σᵢ) →
                        Γ ∣ Δ ⊢V⦂ G (arᵢ op) →
                        Γ ∣ Δ ⊢M⦂ X ! (o , i) →
                        --------------------------
                        Γ ∣ Δ ⊢M⦂ X ! op ↓ₑ (o , i)

    promise_↦_`in_ : {X Y : VType}
                        {o o' : O}
                        {i i' : I} → 
                        (op : Σᵢ) →
                        {_ : lkpᵢ op i ≡ just (o' , i')} →
                        (Γ ∷ G (arᵢ op)) ∣ Δ ⊢M⦂ X ! (o' , i') →
                        Γ ∣ (Δ ∷ X) ⊢M⦂ Y ! (o , i) →
                        ---------------------------------------
                        Γ ∣ Δ ⊢M⦂ Y ! (o , i)

    await_until_      : {X : VType}
                        {C : CType} → 
                        Γ ∣ Δ ⊢V⦂ ⟨ X ⟩ →
                        Γ ∣ (Δ ∷ X) ⊢M⦂ C →
                        -------------------
                        Γ ∣ Δ ⊢M⦂ C
                        
