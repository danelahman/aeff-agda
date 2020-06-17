open import Data.Empty
open import Data.List hiding ([_]) renaming (_∷_ to _∷ₗ_)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
open import AwaitingComputations
open import EffectAnnotations
open import Preservation
open import Progress
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module Finality where


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- WITH INLINED EVALUATION CONTEXT RULES

mutual

  infix 10 _↝↝_

  data _↝↝_ {Γ : Ctx} : {C : CType} → Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

    -- COMPUTATIONAL RULES

    apply           : {X : VType}
                      {C : CType} →
                      (M : Γ ∷ X ⊢M⦂ C) →
                      (V : Γ ⊢V⦂ X) →
                      ----------------------
                      (ƛ M) · V
                      ↝↝
                      M [ id-subst [ V ]s ]m

    let-return      : {X Y : VType}
                      {o : O}
                      {i : I} → 
                      (V : Γ ⊢V⦂ X) →
                      (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                      -----------------------------
                      let= (return V) `in N
                      ↝↝
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
                      ↝↝
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
                      ↝↝
                      (promise op ∣ p ↦ M₁ `in (let= M₂ `in (M-rename (comp-ren exchange wk₁) N)))

    letrec-unfold   : {X : VType}
                      {C D : CType}
                      (M : Γ ∷ (X ⇒ C) ∷ X ⊢M⦂ C) →
                      (N : Γ ∷ (X ⇒ C) ⊢M⦂ D) →
                      ----------------------------------------
                      (letrec M `in N)
                      ↝↝
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
                      ↝↝
                      ↑ op' q (strengthen-val {Δ = X ∷ₗ []} V) (promise op ∣ p ↦ M `in N)

    ↓-return        : {X : VType}
                      {o : O}
                      {i : I}
                      {op : Σₛ} →
                      (V : Γ ⊢V⦂ ``(payload op)) →
                      (W : Γ ⊢V⦂ X) →
                      ----------------------------------------------------------------
                      ↓ {o = o} {i = i} op V (return W)
                      ↝↝
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
                      ↝↝
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
                      ↝↝
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
                      ↝↝
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
                      ↝↝
                      M [ id-subst [ V ]s ]m

    -- INLINED EVALUATION CONTEXT RULES

    context-let      : {X Y : VType}
                       {o : O}
                       {i : I} → 
                       {M M' : Γ ⊢M⦂ X ! (o , i)} →
                       {N : Γ ∷ X ⊢M⦂ Y ! (o , i)} →
                       M ↝↝ M' → 
                       -----------------------------
                       let= M `in N
                       ↝↝
                       let= M' `in N

    context-↑        : {X : VType}
                       {o : O}
                       {i : I}
                       {op : Σₛ}
                       {p : op ∈ₒ o}
                       {V : Γ ⊢V⦂ ``(payload op)}
                       {M N : Γ ⊢M⦂ X ! (o , i)} →
                       M ↝↝ N →
                       ---------------------------
                       ↑ op p V M
                       ↝↝
                       ↑ op p V N

    context-↓        : {X : VType}
                       {o : O}
                       {i : I}
                       {op : Σₛ}
                       {V : Γ ⊢V⦂ ``(payload op)}
                       {M N : Γ ⊢M⦂ X ! (o , i)} →
                       M ↝↝ N →
                       ---------------------------
                       ↓ op V M
                       ↝↝
                       ↓ op V N

    context-promise : {X Y : VType}
                      {o o' : O}
                      {i i' : I}
                      {op : Σₛ} →
                      {r : lkpᵢ op i ≡ just (o' , i')}
                      {M : Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i')} →
                      {N N' : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)} →
                      N ↝↝ N' →
                      ------------------------------------------------
                      promise op ∣ r ↦ M `in N
                      ↝↝
                      promise op ∣ r ↦ M `in N'

    context-coerce  : {X : VType}
                      {o o' : O}
                      {i i' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'} → 
                      {M N : Γ ⊢M⦂ X ! (o , i)} →
                      M ↝↝ N →
                      ---------------------------
                      coerce p q M
                      ↝↝
                      coerce p q N

    -- COERCION RULES

    coerce-return   : {X : VType}
                      {o o' : O}
                      {i i' : I}
                      {p : o ⊑ₒ o'}
                      {q : i ⊑ᵢ i'} → 
                      (V : Γ ⊢V⦂ X) →
                      --------------------------------
                      coerce p q (return V) ↝↝ return V

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
                      ↝↝
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
                      ↝↝
                      promise_∣_↦_`in_ {o' = lkpᵢ-nextₒ q r}
                                       {i' = lkpᵢ-nextᵢ q r}
                                       op
                                       (lkpᵢ-next-eq q r)
                                       (coerce (lkpᵢ-next-⊑ₒ q r) (lkpᵢ-next-⊑ᵢ q r) M)
                                       (coerce p q N)


-- ONE-TO-ONE CORRESPONDENCE BETWEEN THE TWO SETS OF REDUCTION RULES

↝↝-to-↝ : {Γ : Ctx}
          {C : CType}
          {M N : Γ ⊢M⦂ C} → 
          M ↝↝ N →
          -----------------
          M ↝ N

↝↝-to-↝ (apply M V) =
  apply M V
↝↝-to-↝ (let-return V N) =
  let-return V N
↝↝-to-↝ (let-↑ p V M N) =
  let-↑ p V M N
↝↝-to-↝ (let-promise p M₁ M₂ N) =
  let-promise p M₁ M₂ N
↝↝-to-↝ (letrec-unfold M N) =
  letrec-unfold M N
↝↝-to-↝ (promise-↑ p q V M N) =
  promise-↑ p q V M N
↝↝-to-↝ (↓-return V W) =
  ↓-return V W
↝↝-to-↝ (↓-↑ p V W M) =
  ↓-↑ p V W M
↝↝-to-↝ (↓-promise-op p V M N) =
  ↓-promise-op p V M N
↝↝-to-↝ (↓-promise-op' p q V M N) =
  ↓-promise-op' p q V M N
↝↝-to-↝ (await-promise V M) =
  await-promise V M
↝↝-to-↝ (context-let r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-↑ r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-↓ r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-promise r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (context-coerce r) =
  context _ (↝↝-to-↝ r)
↝↝-to-↝ (coerce-return V) =
  coerce-return V
↝↝-to-↝ (coerce-↑ p V M) =
  coerce-↑ p V M
↝↝-to-↝ (coerce-promise p M N) =
  coerce-promise p M N


mutual
  ↝-context-to-↝↝ : {Γ : Ctx}
                    {Δ : BCtx}
                    {C : CType} → 
                    (E : Γ ⊢E[ Δ ]⦂ C) → 
                    {M N : (Γ ⋈ Δ) ⊢M⦂ hole-ty-e E} → 
                    M ↝ N →
                    ---------------------------
                    E [ M ] ↝↝ E [ N ]

  ↝-context-to-↝↝ [-] r =
    ↝-to-↝↝ r
  ↝-context-to-↝↝ (let= E `in x) r =
    context-let (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (↑ op p V E) r =
    context-↑ (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (↓ op V E) r =
    context-↓ (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (promise op ∣ p ↦ M `in E) r =
    context-promise (↝-context-to-↝↝ E r)
  ↝-context-to-↝↝ (coerce p q E) r =
    context-coerce (↝-context-to-↝↝ E r)
  
 
  ↝-to-↝↝ : {Γ : Ctx}
            {C : CType}
            {M N : Γ ⊢M⦂ C} → 
            M ↝ N →
            -----------------
            M ↝↝ N

  ↝-to-↝↝ (apply M V) =
    apply M V
  ↝-to-↝↝ (let-return V N) =
    let-return V N
  ↝-to-↝↝ (let-↑ p V M N) =
    let-↑ p V M N
  ↝-to-↝↝ (let-promise p M₁ M₂ N) =
    let-promise p M₁ M₂ N
  ↝-to-↝↝ (letrec-unfold M N) =
    letrec-unfold M N
  ↝-to-↝↝ (promise-↑ p q V M N) =
    promise-↑ p q V M N
  ↝-to-↝↝ (↓-return V W) =
    ↓-return V W
  ↝-to-↝↝ (↓-↑ p V W M) =
    ↓-↑ p V W M
  ↝-to-↝↝ (↓-promise-op p V M N) =
    ↓-promise-op p V M N
  ↝-to-↝↝ (↓-promise-op' p q V M N) =
    ↓-promise-op' p q V M N
  ↝-to-↝↝ (await-promise V M) =
    await-promise V M
  ↝-to-↝↝ (context E r) =
    ↝-context-to-↝↝ E r
  ↝-to-↝↝ (coerce-return V) =
    coerce-return V
  ↝-to-↝↝ (coerce-↑ p V M) =
    coerce-↑ p V M
  ↝-to-↝↝ (coerce-promise p M N) =
    coerce-promise p M N


-- FINALITY OF RESULT FORMS

run-invert-let : {Γ : Ctx}
                 {X Y : VType}
                 {o : O}
                 {i : I}
                 {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X ! (o , i)}
                 {N : (⟨⟨ Γ ⟩⟩ ∷ X) ⊢M⦂ Y ! (o , i)} →
                 RunResult⟨ Γ ∣ let= M `in N ⟩ →
                 -------------------------------------
                 RunResult⟨ Γ ∣ M ⟩

run-invert-let (awaiting (let-in R)) =
  awaiting R


run-invert-↓ : {Γ : Ctx}
               {X : VType}
               {o : O}
               {i : I}
               {op : Σₛ}
               {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ ``(payload op)}
               {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X ! (o , i)} →
               RunResult⟨ Γ ∣ ↓ op V M ⟩ → 
               -------------------------------
               RunResult⟨ Γ ∣ M ⟩

run-invert-↓ (awaiting (interrupt await)) =
  awaiting await
run-invert-↓ (awaiting (interrupt (let-in R))) =
  awaiting (let-in R)
run-invert-↓ (awaiting (interrupt (interrupt R))) =
  awaiting (interrupt R)
run-invert-↓ (awaiting (interrupt (coerce R))) =
  awaiting (coerce R)


run-invert-promise : {Γ : Ctx}
                     {X Y : VType}
                     {o o' : O}
                     {i i' : I}
                     {op : Σₛ}
                     {p : lkpᵢ op i ≡ just (o' , i')}
                     {M : (⟨⟨ Γ ⟩⟩ ∷ `` (payload op)) ⊢M⦂ (⟨ X ⟩ ! (o' , i'))}
                     {N : (⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩) ⊢M⦂ (Y ! (o , i))} → 
                     RunResult⟨ Γ ∣ (promise op ∣ p ↦ M `in N) ⟩ →
                     --------------------------------------------------------
                     RunResult⟨ Γ ∷ X ∣ N ⟩

run-invert-promise (promise R) =
  R


run-invert-coerce : {Γ : Ctx}
                    {X : VType}
                    {o o' : O}
                    {i i' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'}
                    {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X ! (o , i)} →
                    RunResult⟨ Γ ∣ coerce p q M ⟩ →
                    -------------------------------
                    RunResult⟨ Γ ∣ M ⟩

run-invert-coerce (awaiting (coerce R)) =
  awaiting R


run-apply-⊥ : {Γ : Ctx}
              {X : VType}
              {C : CType}
              {M : (⟨⟨ Γ ⟩⟩ ∷ X) ⊢M⦂ C}
              {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X} →
              RunResult⟨ Γ ∣ ƛ M · V ⟩ →
              --------------------------
              ⊥

run-apply-⊥ (awaiting ())


run-↑-⊥ : {Γ : Ctx}
          {X : VType}
          {o : O}
          {i : I}
          {op : Σₛ}
          {p : op ∈ₒ o}
          {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ ``(payload op)}
          {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ (X ! (o , i))} → 
          RunResult⟨ Γ ∣ ↑ op p V M ⟩ →
          --------------------------------
          ⊥
                 
run-↑-⊥ (awaiting ())


run-let-return-⊥ : {Γ :  Ctx}
                   {X Y : VType}
                   {o : O}
                   {i : I}
                   {V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X}
                   {N : (⟨⟨ Γ ⟩⟩ ∷ X) ⊢M⦂ (Y ! (o , i))} →
                   RunResult⟨ Γ ∣ let= return V `in N ⟩ →
                   --------------------------------------
                   ⊥

run-let-return-⊥ (awaiting (let-in ()))


run-let-promise-⊥ : {Γ : Ctx}
                    {X Y Z : VType}
                    {o o' : O}
                    {i i' : I}
                    {op : Σₛ}
                    {p : lkpᵢ op i ≡ just (o' , i')}
                    {M₁ : (⟨⟨ Γ ⟩⟩ ∷ `` (payload op)) ⊢M⦂ (⟨ X ⟩ ! (o' , i'))}
                    {M₂ : (⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩) ⊢M⦂ (Y ! (o , i))}
                    {N  : (⟨⟨ Γ ⟩⟩ ∷ Y) ⊢M⦂ (Z ! (o , i))} →
                    RunResult⟨ Γ ∣ let= promise op ∣ p ↦ M₁ `in M₂ `in N ⟩ →
                    ----------------------------------------------------------
                    ⊥

run-let-promise-⊥ (awaiting (let-in ()))

run-finality↝↝ : {Γ : Ctx}
                 {C : CType}
                 {M N : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
                 RunResult⟨ Γ ∣ M ⟩ →
                 M ↝↝ N →
                 -----------------------
                 ⊥

run-finality↝↝ (awaiting ()) (apply M V)
run-finality↝↝ R (let-return V N) =
  run-let-return-⊥ R
run-finality↝↝ R (let-↑ p V M N) =
  run-↑-⊥ (run-invert-let R)
run-finality↝↝ R (let-promise p M₁ M₂ N) =
  run-let-promise-⊥ R
run-finality↝↝ (awaiting ()) (letrec-unfold M N)
run-finality↝↝ (promise (awaiting ())) (promise-↑ p q V M N)
run-finality↝↝ (awaiting (interrupt ())) (↓-return V W)
run-finality↝↝ (awaiting (interrupt ())) (↓-↑ p V W M)
run-finality↝↝ (awaiting (interrupt ())) (↓-promise-op p V M N)
run-finality↝↝ (awaiting (interrupt ())) (↓-promise-op' p q V M N)
run-finality↝↝ (awaiting ()) (await-promise V M)
run-finality↝↝ R (context-let r) =
  run-finality↝↝ (run-invert-let R) r
run-finality↝↝ R (context-↑ r) =
  run-↑-⊥ R
run-finality↝↝ R (context-↓ r) =
  run-finality↝↝ (run-invert-↓ R) r
run-finality↝↝ R (context-promise r) =
  run-finality↝↝ (run-invert-promise R) r
run-finality↝↝ R (context-coerce r) =
  run-finality↝↝ (run-invert-coerce R) r
run-finality↝↝ (awaiting (coerce ())) (coerce-return V)
run-finality↝↝ (awaiting (coerce ())) (coerce-↑ p V M)
run-finality↝↝ (awaiting (coerce ())) (coerce-promise p M N)


comp-finality↝↝ : {Γ : Ctx}
                  {C : CType}
                  {M N : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
                  CompResult⟨ Γ ∣ M ⟩ →
                  M ↝↝ N →
                  -----------------------
                  ⊥

comp-finality↝↝ (comp R) r =
  run-finality↝↝ R r
comp-finality↝↝ (signal R) (context-↑ r) =
  comp-finality↝↝ R r


{- LEMMA 3.2 -}

comp-finality : {Γ : Ctx}
                {C : CType}
                {M N : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
                CompResult⟨ Γ ∣ M ⟩ →
                M ↝ N →
                -----------------------
                ⊥

comp-finality R r =
  comp-finality↝↝ R (↝-to-↝↝ r)
