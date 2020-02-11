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

data _⊢P⦂_ (Γ : Ctx) : PType → Set where
  
  run     : {X : VType}
            {o : O}
            {i : I} →
            Γ ⊢M⦂ X ! (o , i) →
            -------------------
            Γ ⊢P⦂ (X ! i) ‼ o

  _∥_     : {PP QQ : SkelPType}
            {o : O} → 
            Γ ⊢P⦂ PP ‼ o →
            Γ ⊢P⦂ QQ ‼ o →
            --------------
            Γ ⊢P⦂ (PP ∥ QQ) ‼ o

  ↑       : {PP : SkelPType}
            {o : O}
            (op : Σₒ) →
            op ∈ₒ o →
            Γ ⊢V⦂ ``(arₒ op) →
            Γ ⊢P⦂ PP ‼ o →
            -------------------
            Γ ⊢P⦂ PP ‼ o

  ↓       : {PP : SkelPType}
            {o : O}
            (op : Σᵢ) →
            Γ ⊢V⦂ ``(arᵢ op) →
            Γ ⊢P⦂ PP ‼ o →
            --------------------------------------------------------
            Γ ⊢P⦂ (proj₁ (op ↓-p (PP , o)) ‼ proj₂ (op ↓-p (PP , o)))

  subsume : {PP QQ : PType} → 
            PP ⊑-p QQ →
            Γ ⊢P⦂ PP →
            -----------------
            Γ ⊢P⦂ QQ

  

