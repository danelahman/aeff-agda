open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Data.Maybe
open import Data.Product

open import AEff
open import EffectAnnotations
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module Preservation where


-- BINDING CONTEXTS

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
                     (op : Σₛ) →
                     op ∈ₒ o →
                     Γ ⊢V⦂ ``(payload op) →
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     ------------------------
                     Γ ⊢E[ Δ ]⦂ X ! (o , i)

  ↓                : {Δ : BCtx}
                     {X : VType}
                     {o : O}
                     {i : I}
                     (op : Σₛ) →
                     Γ ⊢V⦂ ``(payload op) →
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     ---------------------------
                     Γ ⊢E[ Δ ]⦂ X ! op ↓ₑ (o , i)

  promise_∣_↦_`in_ : {Δ : BCtx}
                     {X Y : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (op : Σₛ) →
                     lkpᵢ op i ≡ just (o' , i') →
                     Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i') →
                     Γ ∷ ⟨ X ⟩ ⊢E[ Δ ]⦂ Y ! (o , i) →
                     ------------------------------------------
                     Γ ⊢E[ X ∷ₗ Δ ]⦂ Y ! (o , i)

  coerce           : {Δ : BCtx}
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
Γ ⋈ (X ∷ₗ Δ) = (Γ ∷ ⟨ X ⟩) ⋈ Δ


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
hole-ty-e (coerce p q E) =
  hole-ty-e E


-- FILLING A WELL-TYPED EVALUATION CONTEXT

{- LEMMA 3.5 -}

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
coerce p q E [ M ] =
  coerce p q (E [ M ])


-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-var : {Γ : Ctx} → (Δ : BCtx) → {A : BType} → `` A ∈ Γ ⋈ Δ → `` A ∈ Γ
strengthen-var [] x = x
strengthen-var (y ∷ₗ Δ) x with strengthen-var Δ x
... | Tl p = p


strengthen-val : {Γ : Ctx} {Δ : BCtx} {A : BType} → Γ ⋈ Δ ⊢V⦂ `` A → Γ ⊢V⦂ `` A
strengthen-val {_} {Δ} (` x) =
  ` strengthen-var Δ x
strengthen-val (``_ c) =
  ``_ c

strengthen-val-[] : {Γ : Ctx}
                    {A : BType} → 
                    (V : Γ ⋈ [] ⊢V⦂ `` A) →
                    --------------------
                    strengthen-val {Δ = []} V ≡ V

strengthen-val-[] (` x) =
  refl
strengthen-val-[] (``_ c) =
  refl


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

{- THEOREM 3.6 -}

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
                    {op : Σₛ} →
                    (p : op ∈ₒ o) →
                    (V : Γ ⊢V⦂ ``(payload op)) →
                    (M : Γ ⊢M⦂ X ! (o , i)) →
                    (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                    -----------------------------
                    let= (↑ op p V M) `in N
                    ↝
                    ↑ op p V (let= M `in N)

  let-promise     : {X Y Z : VType}
                    {o o' : O}
                    {i i' : I}
                    {op : Σₛ} →
                    (p : lkpᵢ op i ≡ just (o' , i')) →
                    (M₁ : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i')) →
                    (M₂ : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                    (N : Γ ∷ Y ⊢M⦂ Z ! (o , i)) →
                    ---------------------------------------------------------------------------
                    let= (promise op ∣ p ↦ M₁ `in M₂) `in N
                    ↝
                    (promise op ∣ p ↦ M₁ `in (let= M₂ `in (M-rename (comp-ren exchange wk₁) N)))

  letrec-unfold   : {X : VType}
                    {C D : CType}
                    (M : Γ ∷ (X ⇒ C) ∷ X ⊢M⦂ C) →
                    (N : Γ ∷ (X ⇒ C) ⊢M⦂ D) →
                    ----------------------------------------
                    (letrec M `in N)
                    ↝
                    N [ id-subst [ ƛ (letrec M-rename wk₃ M `in M-rename exchange M) ]s ]m

  promise-↑       : {X Y : VType}
                    {o o' : O}
                    {i i' : I}
                    {op op' : Σₛ} →
                    (p : lkpᵢ op i ≡ just (o' , i')) →
                    (q : op' ∈ₒ o) →
                    (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``(payload op')) → 
                    (M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i')) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                    --------------------------------------------
                    (promise op ∣ p ↦ M `in (↑ op' q V N))
                    ↝
                    ↑ op' q (strengthen-val {Δ = X ∷ₗ []} V) (promise op ∣ p ↦ M `in N)

  ↓-return        : {X : VType}
                    {o : O}
                    {i : I}
                    {op : Σₛ} →
                    (V : Γ ⊢V⦂ ``(payload op)) →
                    (W : Γ ⊢V⦂ X) →
                    ----------------------------------------------------------------
                    ↓ {o = o} {i = i} op V (return W)
                    ↝
                    return {o = proj₁ (op ↓ₑ (o , i))} {i = proj₂ (op ↓ₑ (o , i))} W

  ↓-↑             : {X : VType}
                    {o : O}
                    {i : I}
                    {op : Σₛ}
                    {op' : Σₛ} →
                    (p : op' ∈ₒ o) →
                    (V : Γ ⊢V⦂ ``(payload op)) →
                    (W : Γ ⊢V⦂ ``(payload op')) →
                    (M : Γ ⊢M⦂ X ! (o , i)) →
                    -------------------------------
                    ↓ op V (↑ op' p W M)
                    ↝
                    ↑ op' (↓ₑ-⊑ₒ op' p) W (↓ op V M)

  ↓-promise-op    : {X Y : VType}
                    {o o' : O}
                    {i i' : I}
                    {op : Σₛ} →
                    (p : lkpᵢ op i ≡ just (o' , i')) →
                    (V : Γ ⊢V⦂ ``(payload op)) → 
                    (M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i')) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                    ---------------------------------------------------------------------------------------
                    ↓ op V (promise op ∣ p ↦ M `in N )
                    ↝
                    (let= (coerce (↓ₑ-⊑ₒ-o' {o} p) (↓ₑ-⊑ₒ-i' {o} p) (M [ id-subst [ V ]s ]m)) `in
                      ↓ op (V-rename wk₁ V) ((M-rename (comp-ren exchange wk₁) N) [ id-subst [ ` Hd ]s ]m))

  ↓-promise-op'   : {X Y : VType}
                    {o o' : O}
                    {i i' : I}
                    {op op' : Σₛ} →
                    (p : ¬ op ≡ op') →
                    (q : lkpᵢ op' i ≡ just (o' , i')) →
                    (V : Γ ⊢V⦂ ``(payload op)) → 
                    (M : Γ ∷ ``(payload op') ⊢M⦂ ⟨ X ⟩ ! (o' , i')) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                    ------------------------------------------------------------------------------------------
                    ↓ op V (promise op' ∣ q ↦ M `in N )
                    ↝
                    promise_∣_↦_`in_ {o' = proj₁ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q)}
                                     {i' = proj₁ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q))}
                                     op'
                                     (proj₁ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q))))
                                     (coerce (proj₁ (proj₂ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} p q)))))
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

  -- EVALUATION CONTEXT RULE

  context         : {Δ : BCtx}
                    {C : CType} → 
                    (E : Γ ⊢E[ Δ ]⦂ C) →
                    {M N : Γ ⋈ Δ ⊢M⦂ (hole-ty-e E)} →
                    M ↝ N →
                    -------------------------------
                    E [ M ] ↝ E [ N ]

  -- COERCION RULES
  -- (THE RESULT OF WORKING WITH WELL-TYPED SYNTAX AND MAKING SUBSUMPTION INTO AN EXPLICIT COERCION)

  coerce-return   : {X : VType}
                    {o o' : O}
                    {i i' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'} → 
                    (V : Γ ⊢V⦂ X) →
                    --------------------------------
                    coerce p q (return V) ↝ return V

  coerce-↑        : {X : VType}
                    {o o' : O}
                    {i i' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'}
                    {op : Σₛ} → 
                    (r : op ∈ₒ o) →
                    (V : Γ ⊢V⦂ ``(payload op)) →
                    (M : Γ ⊢M⦂ X ! (o , i)) →
                    -------------------------------
                    coerce p q (↑ op r V M)
                    ↝
                    ↑ op (p op r) V (coerce p q M)

  coerce-promise  : {X Y : VType}
                    {o o' o'' : O}
                    {i i' i'' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'}
                    {op : Σₛ} →
                    (r : lkpᵢ op i ≡ just (o'' , i''))
                    (M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ ! (o'' , i'')) →
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                    ------------------------------------------------------------------
                    coerce p q (promise op ∣ r ↦ M `in N)
                    ↝
                    promise_∣_↦_`in_ {o' = lkpᵢ-nextₒ q r}
                                     {i' = lkpᵢ-nextᵢ q r}
                                     op
                                     (lkpᵢ-next-eq q r)
                                     (coerce (lkpᵢ-next-⊑ₒ q r) (lkpᵢ-next-⊑ᵢ q r) M)
                                     (coerce p q N)
