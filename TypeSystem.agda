open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.Product hiding (Σ)

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Operations
open import Terms
open import Types

module TypeSystem where

infix 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A

Context = SnocList VType

data _⦂_∈_ : ℕ → VType → Context → Set where
  stop : {Γ : Context} {X : VType} →
         0 ⦂ X ∈ Γ ∷ X
  next : {Γ : Context} {X Y : VType} {x : ℕ} →
         x ⦂ X ∈ Γ → (suc x) ⦂ X ∈ Γ ∷ Y

mutual
  data _⊢_⦂_ : Context → VTerm → VType → Set where
    ty-val-var     : {Γ : Context}
                     {x : ℕ}
                     {X : VType} →
                     x ⦂ X ∈ Γ →
                     -------------
                     Γ ⊢ ` x ⦂ X

    ty-val-const   : {Γ : Context}
                     {c : Σ} → 
                     --------------------
                     Γ ⊢ ∣ c ∣ ⦂ G (ar c)

    ty-val-fun     : {Γ : Context}
                     {X : VType}
                     {m : CTerm}
                     {C : CType} →
                     Γ ∷ X ⊢ m ⦂⦂ C → 
                     ---------------
                     Γ ⊢ ƛ m ⦂ X ⇒ C

    ty-val-promise : {Γ : Context}
                     {v : VTerm}
                     {X : VType} →
                     Γ ⊢ v ⦂ X → 
                     -------------------------
                     Γ ⊢ ⟨ v ⟩ ⦂ ⟨ X ⟩

  data _⊢_⦂⦂_ : Context → CTerm → CType → Set where
    ty-comp-return    : {Γ : Context}
                        {v : VTerm}
                        {X : VType}
                        {o : O}
                        {i : I} →
                        Γ ⊢ v ⦂ X →
                        ---------------------------
                        Γ ⊢ return v ⦂⦂ X ! (o , i)

    ty-comp-let       : {Γ : Context}
                        {m n : CTerm}
                        {X Y : VType}
                        {o : O}
                        {i : I} → 
                        Γ ⊢ m ⦂⦂ X ! (o , i) →
                        Γ ∷ X ⊢ n ⦂⦂ Y ! (o , i) →
                        -----------------------------
                        Γ ⊢ `let m `in n ⦂⦂ Y ! (o , i)

    ty-comp-apply     : {Γ : Context}
                        {v w : VTerm}
                        {X : VType}
                        {C : CType} → 
                        Γ ⊢ v ⦂ X ⇒ C →
                        Γ ⊢ w ⦂ X →
                        ------------------
                        Γ ⊢ v · w ⦂⦂ C

    ty-comp-signal    : {Γ : Context}
                        {op : Σₒ}
                        {v : VTerm}
                        {m : CTerm}
                        {X : VType}
                        {o : O}
                        {i : I} →
                        op ∈ₒ o → 
                        Γ ⊢ v ⦂ G (arₒ op) →
                        Γ ⊢ m ⦂⦂ X ! (o , i) → 
                        --------------------------------
                        Γ ⊢ ↑ op v m ⦂⦂ X ! (o , i)
                     
    ty-comp-interrupt : {Γ : Context}
                        {op : Σᵢ}
                        {v : VTerm}
                        {m : CTerm}
                        {X : VType}
                        {o : O}
                        {i : I} →
                        Γ ⊢ v ⦂ G (arᵢ op) →
                        Γ ⊢ m ⦂⦂ X ! (o , i) → 
                        -----------------------------------
                        Γ ⊢ ↓ op v m ⦂⦂ X ! (op ↓ₑ (o , i))

    ty-comp-promise  : {Γ : Context}
                       {op : Σᵢ}
                       {m n : CTerm}
                       {X Y : VType}
                       {o o' : O}
                       {i i' : I} →
                       lkpᵢ op i ≡ just (o' , i') →
                       Γ ∷ G (arᵢ op) ⊢ m ⦂⦂ X ! (o' , i') →
                       Γ ∷ X ⊢ n ⦂⦂ Y ! (o , i) → 
                       ---------------------------------------------
                       Γ ⊢ promise op ↦ m `as X `in n ⦂⦂ Y ! (o , i)

    ty-comp-await   : {Γ : Context}
                      {v : VTerm}
                      {m : CTerm}
                      {X : VType}
                      {C : CType} → 
                      Γ ⊢ v ⦂ ⟨ X ⟩ →
                      Γ ∷ X ⊢ m ⦂⦂ C →
                      ------------------------
                      Γ ⊢ await v until m ⦂⦂ C

