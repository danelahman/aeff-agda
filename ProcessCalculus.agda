open import Data.Maybe
open import Data.Product hiding (Σ)

open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

open import Calculus
open import EffectAnnotations
open import ProcessTypes
open import Types

module ProcessCalculus where


-- DERIVATIONS OF WELL-TYPED PROCESSES

infix 10 _⊢P⦂_

data _⊢P⦂_ (Γ : Ctx) : {o : O} → PType o → Set where

  run     : {X : VType}
            {o : O}
            {i : I} →
            Γ ⊢M⦂ X ! (o , i) →
            -------------------
            Γ ⊢P⦂ X ‼ o , i

  _∥_     : {o o' : O}
            {PP : PType o} →
            {QQ : PType o'} → 
            Γ ⊢P⦂ PP →
            Γ ⊢P⦂ QQ →
            --------------
            Γ ⊢P⦂ (PP ∥ QQ)

  ↑       : {o : O} →
            {PP : PType o}
            (op : Σₙ) →
            op ∈ₒ o →
            Γ ⊢V⦂ ``(arₙ op) →
            Γ ⊢P⦂ PP →
            -------------------
            Γ ⊢P⦂ PP

  ↓       : {o : O}
            {PP : PType o}
            (op : Σₙ) →
            Γ ⊢V⦂ ``(arₙ op) →
            Γ ⊢P⦂ PP →
            ------------------
            Γ ⊢P⦂ op ↓ₚ PP




{-
-- DERIVATIONS OF WELL-TYPED PROCESSES

infix 10 _⊢P⦂_

data _⊢P⦂_ (Γ : Ctx) : PType → Set where
  
  run     : {X : VType}
            {o : O}
            {i : I} →
            Γ ⊢M⦂ X ! (o , i) →
            -------------------
            Γ ⊢P⦂ (X ! i) ‼ o

  _∥_     : {PP QQ : PTypeShape}
            {o : O} → 
            Γ ⊢P⦂ PP ‼ o →
            Γ ⊢P⦂ QQ ‼ o →
            --------------
            Γ ⊢P⦂ (PP ∥ QQ) ‼ o

  ↑       : {PP : PTypeShape}
            {o : O}
            (op : Σₙ) →
            op ∈ₒ o →
            Γ ⊢V⦂ ``(arₙ op) →
            Γ ⊢P⦂ PP ‼ o →
            -------------------
            Γ ⊢P⦂ PP ‼ o

  ↓       : {PP : PTypeShape}
            {o : O}
            (op : Σₙ) →
            Γ ⊢V⦂ ``(arₙ op) →
            Γ ⊢P⦂ PP ‼ o →
            ------------------------------------------------------
            Γ ⊢P⦂ (proj₁ (op ↓ₚ (PP , o)) ‼ proj₂ (op ↓ₚ (PP , o)))

  subsume : {PP PP' : PTypeShape}
            {o o' : O} → 
            PP ⊑ₚ PP' →
            o ⊑ₒ o' →
            Γ ⊢P⦂ PP ‼ o →
            -----------------
            Γ ⊢P⦂ PP' ‼ o'

  -}

