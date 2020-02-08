open import Data.Maybe
open import Data.Product

open import Calculus
open import Operations
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])

module OpSemantics where

data _⊢E⦂_ (Γ : Ctx) : CType → Set where

  [_]              : {C : CType} →
                     Γ ⊢M⦂ C → 
                     -------------
                     Γ ⊢E⦂ C

  let=_`in_        : {X Y : VType}
                     {o : O}
                     {i : I} →
                     Γ ⊢E⦂ X ! (o , i) →
                     Γ ∷ X ⊢M⦂ Y ! (o , i) →
                     -----------------------
                     Γ ⊢E⦂ Y ! (o , i)

  ↑                : {X : VType}
                     {o : O}
                     {i : I} →
                     (op : Σₒ) →
                     op ∈ₒ o →
                     Γ ⊢V⦂ ``(arₒ op) →
                     Γ ⊢E⦂ X ! (o , i) →
                     -------------------
                     Γ ⊢E⦂ X ! (o , i)

  ↓                : {X : VType}
                     {o : O}
                     {i : I}
                     (op : Σᵢ) →
                     Γ ⊢V⦂ ``(arᵢ op) →
                     Γ ⊢E⦂ X ! (o , i) →
                     ----------------------
                     Γ ⊢E⦂ X ! op ↓ₑ (o , i)

  promise_∣_↦_`in_ : {X Y : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (op : Σᵢ) →
                     lkpᵢ op i ≡ just (o' , i') →
                     Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i') →
                     Γ ∷ ⟨ X ⟩ ⊢E⦂ Y ! (o , i) →
                     ---------------------------------
                     Γ ⊢E⦂ Y ! (o , i)

mutual

  infix 10 _↝_

  data _↝_ {Γ : Ctx} : {C : CType} → Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

    apply      : {X : VType}
                 {C : CType} →
                 (M : Γ ∷ X ⊢M⦂ C) →
                 (V : Γ ⊢V⦂ X) →
                 ----------------------
                 (ƛ M) · V
                 ↝
                 M [ id-subst [ V ]ₛ ]ₘ

    let-return : {X Y : VType}
                 {o : O}
                 {i : I} → 
                 (V : Γ ⊢V⦂ X) →
                 (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                 -----------------------------
                 let= (return V) `in N
                 ↝
                 N [ id-subst [ V ]ₛ ]ₘ

    let-↑ : {X Y : VType}
            {o : O}
            {i : I}
            {op : Σₒ} →
            (p : op ∈ₒ o) →
            (V : Γ ⊢V⦂ ``(arₒ op)) →
            (M : Γ ⊢M⦂ X ! (o , i)) →
            (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
            -----------------------------
            let= (↑ op p V M) `in N
            ↝
            ↑ op p V (let= M `in N)

    let-promise : {X Y Z : VType}
                  {o o' : O}
                  {i i' : I}
                  {op : Σᵢ} →
                  (p : lkpᵢ op i ≡ just (o' , i')) →
                  (M₁ : Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i')) →
                  (M₂ : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                  (N : Γ ∷ Y ⊢M⦂ Z ! (o , i)) →
                  ---------------------------------------------------------------------------
                  let= (promise op ∣ p ↦ M₁ `in M₂) `in N
                  ↝
                  (promise op ∣ p ↦ M₁ `in (let= M₂ `in (M-rename (comp-ren exchange wk₁) N)))

    ↓-return : {X : VType}
               {o : O}
               {i : I}
               {op : Σᵢ} →
               (V : Γ ⊢V⦂ ``(arᵢ op)) →
               (W : Γ ⊢V⦂ X) →
               ---------------------------------------------------------------
               ↓ {o = o} {i = i} op V (return W)
               ↝
               return {o = proj₁ (op ↓ₑ (o , i))} {i = proj₂ (op ↓ₑ (o , i))} W

    ↓-↑      : {X : VType}
               {o : O}
               {i : I}
               {op : Σᵢ}
               {op' : Σₒ} →
               (p : op' ∈ₒ o) →
               (V : Γ ⊢V⦂ ``(arᵢ op)) →
               (W : Γ ⊢V⦂ ``(arₒ op')) →
               (M : Γ ⊢M⦂ X ! (o , i)) →
               -----------------------------------
               ↓ op V (↑ op' p W M)
               ↝
               ↑ op' (opₒ-in-↓ₑ-lem p) W (↓ op V M)

    ↓-promise-op : {X Y : VType}
                   {o o' : O}
                   {i i' : I}
                   {op : Σᵢ} →
                   (p : lkpᵢ op i ≡ just (o' , i')) →
                   (V : Γ ⊢V⦂ ``(arᵢ op)) → 
                   (M : Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i')) →
                   (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                   ---------------------------------------
                   ↓ op V (promise op ∣ p ↦ M `in N )
                   ↝
                   (let= (coerce (⊑ₒ-↓ₑ-o'-lem {o} p) (⊑ᵢ-↓ₑ-i'-lem {o} p) (M [ id-subst [ V ]ₛ ]ₘ)) `in
                     ↓ op (V-rename wk₁ V) ((M-rename (comp-ren exchange wk₁) N) [ id-subst [ ⟨ ` Hd ⟩ ]ₛ ]ₘ))

    

  data _↝ₑ_ {Γ : Ctx} {C : CType} : Γ ⊢E⦂ C → Γ ⊢E⦂ C → Set where
