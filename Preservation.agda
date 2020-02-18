open import Data.List hiding ([_]) renaming (_∷_ to _∷∷_)
open import Data.Maybe
open import Data.Product

open import Calculus
open import EffectAnnotations
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module Preservation where

-- Binding contexts

BCtx = List VType


-- WELL-TYPED EVALUATION CONTEXTS

data _⊢E[_]⦂_ (Γ : Ctx) : (Δ : BCtx) → CType → Set where

  [-]              : {C : CType} → 
                     -------------
                     Γ ⊢E[ [] ]⦂ C

  let=_`in_        : {Δ : BCtx}
                     {X Y : VType}
                     {o : O}
                     {i : I} →
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     Γ ∷ X ⊢M⦂ Y ! (o , i) →
                     ------------------------
                     Γ ⊢E[ Δ ]⦂ Y ! (o , i)

  ↑                : {Δ : BCtx}
                     {X : VType}
                     {o : O}
                     {i : I} →
                     (op : Σₙ) →
                     op ∈ₒ o →
                     Γ ⊢V⦂ ``(arₙ op) →
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     ------------------------
                     Γ ⊢E[ Δ ]⦂ X ! (o , i)

  ↓                : {Δ : BCtx}
                     {X : VType}
                     {o : O}
                     {i : I}
                     (op : Σₙ) →
                     Γ ⊢V⦂ ``(arₙ op) →
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     ---------------------------
                     Γ ⊢E[ Δ ]⦂ X ! op ↓ₑ (o , i)

  promise_∣_↦_`in_ : {Δ : BCtx}
                     {X Y : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (op : Σₙ) →
                     lkpᵢ op i ≡ just (o' , i') →
                     Γ ∷ ``(arₙ op) ⊢M⦂ X ! (o' , i') →
                     Γ ∷ ⟨ X ⟩ ⊢E[ Δ ]⦂ Y ! (o , i) →
                     ----------------------------------
                     Γ ⊢E[ X ∷∷ Δ ]⦂ Y ! (o , i)

  subsume          : {Δ : BCtx}
                     {X : VType}
                     {o o' : O}
                     {i i' : I} →
                     o ⊑ₒ o' →
                     i ⊑ᵢ i' → 
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     ------------------------
                     Γ ⊢E[ Δ ]⦂ X ! (o' , i')


-- MERGING AN ORDINARY CONTEXT AND A BINDING CONTEXT

infix 30 _⋈_

_⋈_ : Ctx → BCtx → Ctx
Γ ⋈ [] = Γ
Γ ⋈ (X ∷∷ Δ) = (Γ ∷ ⟨ X ⟩) ⋈ Δ


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED EVALUATION CONTEXT

hole-ty-e : {Γ : Ctx} {Δ : BCtx} {C : CType} → Γ ⊢E[ Δ ]⦂ C → CType
hole-ty-e {_} {_} {C} [-] =
  C
hole-ty-e (let= E `in M) =
  hole-ty-e E
hole-ty-e (↑ op p V E) =
  hole-ty-e E
hole-ty-e (↓ op V E) =
  hole-ty-e E
hole-ty-e (promise op ∣ p ↦ M `in E) =
  hole-ty-e E
hole-ty-e (subsume p q E) =
  hole-ty-e E


-- FILLING A WELL-TYPED EVALUATION CONTEXT

infix 30 _[_]

_[_] : {Γ : Ctx} {Δ : BCtx} {C : CType} → (E : Γ ⊢E[ Δ ]⦂ C) → Γ ⋈ Δ ⊢M⦂ (hole-ty-e E) → Γ ⊢M⦂ C
[-] [ M ] =
  M
(let= E `in N) [ M ] =
  let= (E [ M ]) `in N
↑ op p V E [ M ] =
  ↑ op p V (E [ M ])
↓ op V E [ M ] =
  ↓ op V (E [ M ])
(promise op ∣ p ↦ N `in E) [ M ] =
  promise op ∣ p ↦ N `in (E [ M ])
subsume p q E [ M ] =
  subsume p q (E [ M ])


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

mutual

  infix 10 _↝_

  data _↝_ {Γ : Ctx} : {C : CType} → Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

    -- COMPUTATIONAL RULES

    apply           : {X : VType}
                      {C : CType} →
                      (M : Γ ∷ X ⊢M⦂ C) →
                      (V : Γ ⊢V⦂ X) →
                      ----------------------
                      (ƛ M) · V
                      ↝
                      M [ id-subst [ V ]s ]m

    let-return      : {X Y : VType}
                      {o : O}
                      {i : I} → 
                      (V : Γ ⊢V⦂ X) →
                      (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                      -----------------------------
                      let= (return V) `in N
                      ↝
                      N [ id-subst [ V ]s ]m

    let-↑           : {X Y : VType}
                      {o : O}
                      {i : I}
                      {op : Σₙ} →
                      (p : op ∈ₒ o) →
                      (V : Γ ⊢V⦂ ``(arₙ op)) →
                      (M : Γ ⊢M⦂ X ! (o , i)) →
                      (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                      -----------------------------
                      let= (↑ op p V M) `in N
                      ↝
                      ↑ op p V (let= M `in N)

    let-promise     : {X Y Z : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₙ} →
                      (p : lkpᵢ op i ≡ just (o' , i')) →
                      (M₁ : Γ ∷ ``(arₙ op) ⊢M⦂ X ! (o' , i')) →
                      (M₂ : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                      (N : Γ ∷ Y ⊢M⦂ Z ! (o , i)) →
                      ---------------------------------------------------------------------------
                      let= (promise op ∣ p ↦ M₁ `in M₂) `in N
                      ↝
                      (promise op ∣ p ↦ M₁ `in (let= M₂ `in (M-rename (comp-ren exchange wk₁) N)))

    ↓-return        : {X : VType}
                      {o : O}
                      {i : I}
                      {op : Σₙ} →
                      (V : Γ ⊢V⦂ ``(arₙ op)) →
                      (W : Γ ⊢V⦂ X) →
                      ---------------------------------------------------------------
                      ↓ {o = o} {i = i} op V (return W)
                      ↝
                      return {o = proj₁ (op ↓ₑ (o , i))} {i = proj₂ (op ↓ₑ (o , i))} W

    ↓-↑             : {X : VType}
                      {o : O}
                      {i : I}
                      {op : Σₙ}
                      {op' : Σₙ} →
                      (p : op' ∈ₒ o) →
                      (V : Γ ⊢V⦂ ``(arₙ op)) →
                      (W : Γ ⊢V⦂ ``(arₙ op')) →
                      (M : Γ ⊢M⦂ X ! (o , i)) →
                      -------------------------------
                      ↓ op V (↑ op' p W M)
                      ↝
                      ↑ op' (↓ₑ-⊑ₒ op' p) W (↓ op V M)

    ↓-promise-op    : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₙ} →
                      (p : lkpᵢ op i ≡ just (o' , i')) →
                      (V : Γ ⊢V⦂ ``(arₙ op)) → 
                      (M : Γ ∷ ``(arₙ op) ⊢M⦂ X ! (o' , i')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                      ------------------------------------------------------------------------------------------
                      ↓ op V (promise op ∣ p ↦ M `in N )
                      ↝
                      (let= (subsume (↓ₑ-⊑ₒ-o' {o} p) (↓ₑ-⊑ₒ-i' {o} p) (M [ id-subst [ V ]s ]m)) `in
                        ↓ op (V-rename wk₁ V) ((M-rename (comp-ren exchange wk₁) N) [ id-subst [ ⟨ ` Hd ⟩ ]s ]m))

    ↓-promise-op'   : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op op' : Σₙ} →
                      (p : ¬ op ≡ op') →
                      (q : lkpᵢ op' i ≡ just (o' , i')) →
                      (V : Γ ⊢V⦂ ``(arₙ op)) → 
                      (M : Γ ∷ ``(arₙ op') ⊢M⦂ X ! (o' , i')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                      ---------------------------------------------------------------------------------------
                      ↓ op V (promise op' ∣ q ↦ M `in N )
                      ↝
                      promise_∣_↦_`in_ {o' = proj₁ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q)}
                                       {i' = proj₁ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q))}
                                       op'
                                       (proj₁ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q))))
                                       (subsume (proj₁ (proj₂ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q)))))
                                                (proj₂ (proj₂ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q)))))
                                                M)
                                       (↓ op (V-rename wk₁ V) N)

    await-promise   : {X : VType}
                      {C : CType} → 
                      (V : Γ ⊢V⦂ X) → 
                      (M : Γ ∷ X ⊢M⦂ C) →
                      --------------------
                      await ⟨ V ⟩ until M
                      ↝
                      M [ id-subst [ V ]s ]m

    -- EVALUATION CONTEXT RULE (ALSO CAPTURES THE SUBSUMPTION CONGRUENCE)

    context         : {Δ : BCtx}
                      {C : CType} → 
                      (E : Γ ⊢E[ Δ ]⦂ C) →
                      {M N : Γ ⋈ Δ ⊢M⦂ (hole-ty-e E)} →
                      M ↝ N →
                      -------------------------------
                      E [ M ] ↝ E [ N ]

    -- SUBSUMPTION RULES
    -- (ADMINISTRATIVE, NEEDED FOR PROGRESS, RESULT OF WORKING WITH WELL-TYPED SYNTAX)

    subsume-return  : {X : VType}
                      {o o' : O}
                      {i i' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'} → 
                      (V : Γ ⊢V⦂ X) →
                      ---------------------------------
                      subsume p q (return V) ↝ return V

    subsume-let     : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'} →
                      (M : Γ ⊢M⦂ X ! (o , i)) →
                      (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                      ----------------------------------------
                      subsume p q (let= M `in N)
                      ↝
                      let= (subsume p q M) `in (subsume p q N)

    subsume-↑       : {X : VType}
                      {o o' : O}
                      {i i' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'}
                      {op : Σₙ} → 
                      (r : op ∈ₒ o) →
                      (V : Γ ⊢V⦂ ``(arₙ op)) →
                      (M : Γ ⊢M⦂ X ! (o , i)) →
                      -------------------------------
                      subsume p q (↑ op r V M)
                      ↝
                      ↑ op (p op r) V (subsume p q M)                      

    subsume-promise : {X Y : VType}
                      {o o' o'' : O}
                      {i i' i'' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'}
                      {op : Σₙ} →
                      (r : lkpᵢ op i ≡ just (o'' , i''))
                      (M : Γ ∷ ``(arₙ op) ⊢M⦂ X ! (o'' , i'')) →
                      (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                      ----------------------------------------------------------------
                      subsume p q (promise op ∣ r ↦ M `in N)
                      ↝
                      promise_∣_↦_`in_ {o' = lkpᵢ-nextₒ q r}
                                       {i' = lkpᵢ-nextᵢ q r}
                                       op
                                       (lkpᵢ-next-eq q r)
                                       (subsume (lkpᵢ-next-⊑ₒ q r) (lkpᵢ-next-⊑ᵢ q r) M)
                                       (subsume p q N)

    subsume-subsume : {X : VType}
                      {o o' o'' : O}
                      {i i' i'' : I}
                      {p : o ⊑ₒ o'}
                      {p' : o' ⊑ₒ o''}
                      {q : i ⊑ᵢ i'}
                      {q' : i' ⊑ᵢ i''} →
                      (M : Γ ⊢M⦂ X ! (o , i)) →
                      ----------------------------------------
                      subsume p' q' (subsume p q M)
                      ↝
                      subsume (⊑ₒ-trans p p') (⊑ᵢ-trans q q') M
