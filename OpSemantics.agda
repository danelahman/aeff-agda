open import Data.Maybe
open import Data.Product

open import Calculus
open import Operations
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

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

  coerce           : {X : VType}
                     {o o' : O}
                     {i i' : I} →
                     o ⊑ₒ o' →
                     i ⊑ᵢ i' → 
                     Γ ⊢E⦂ X ! (o , i) →
                     -------------------
                     Γ ⊢E⦂ X ! (o' , i')


⌈_⌉ : {Γ : Ctx} {C : CType} → Γ ⊢E⦂ C → Γ ⊢M⦂ C
⌈ [ M ] ⌉ = M
⌈ let= E `in N ⌉ = let= ⌈ E ⌉ `in N
⌈ ↑ op p V E ⌉ = ↑ op p V ⌈ E ⌉
⌈ ↓ op V E ⌉ = ↓ op V ⌈ E ⌉
⌈ promise op ∣ p ↦ M `in E ⌉ = promise op ∣ p ↦ M `in ⌈ E ⌉
⌈ coerce p q E ⌉ = coerce p q ⌈ E ⌉


mutual

  infix 10 _↝_
  infix 10 _↝ₑ_

  data _↝_ {Γ : Ctx} : {C : CType} → Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

    -- COMPUTATIONAL RULES

    apply          : {X : VType}
                     {C : CType} →
                     (M : Γ ∷ X ⊢M⦂ C) →
                     (V : Γ ⊢V⦂ X) →
                     ----------------------
                     (ƛ M) · V
                     ↝
                     M [ id-subst [ V ]ₛ ]ₘ

    let-return     : {X Y : VType}
                     {o : O}
                     {i : I} → 
                     (V : Γ ⊢V⦂ X) →
                     (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                     -----------------------------
                     let= (return V) `in N
                     ↝
                     N [ id-subst [ V ]ₛ ]ₘ

    let-↑          : {X Y : VType}
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

    let-promise    : {X Y Z : VType}
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

    ↓-return       : {X : VType}
                     {o : O}
                     {i : I}
                     {op : Σᵢ} →
                     (V : Γ ⊢V⦂ ``(arᵢ op)) →
                     (W : Γ ⊢V⦂ X) →
                     ---------------------------------------------------------------
                     ↓ {o = o} {i = i} op V (return W)
                     ↝
                     return {o = proj₁ (op ↓ₑ (o , i))} {i = proj₂ (op ↓ₑ (o , i))} W

    ↓-↑            : {X : VType}
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

    ↓-promise-op   : {X Y : VType}
                     {o o' : O}
                     {i i' : I}
                     {op : Σᵢ} →
                     (p : lkpᵢ op i ≡ just (o' , i')) →
                     (V : Γ ⊢V⦂ ``(arᵢ op)) → 
                     (M : Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i')) →
                     (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                     ------------------------------------------------------------------------------------------
                     ↓ op V (promise op ∣ p ↦ M `in N )
                     ↝
                     (let= (coerce (⊑ₒ-↓ₑ-o'-lem {o} p) (⊑ᵢ-↓ₑ-i'-lem {o} p) (M [ id-subst [ V ]ₛ ]ₘ)) `in
                       ↓ op (V-rename wk₁ V) ((M-rename (comp-ren exchange wk₁) N) [ id-subst [ ⟨ ` Hd ⟩ ]ₛ ]ₘ))

    ↓-promise-op'  : {X Y : VType}
                     {o o' : O}
                     {i i' : I}
                     {op op' : Σᵢ} →
                     (p : ¬ op ≡ op') →
                     (q : lkpᵢ op' i ≡ just (o' , i')) →
                     (V : Γ ⊢V⦂ ``(arᵢ op)) → 
                     (M : Γ ∷ ``(arᵢ op') ⊢M⦂ X ! (o' , i')) →
                     (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                     -----------------------------------------------------
                     ↓ op V (promise op' ∣ q ↦ M `in N )
                     ↝
                     promise_∣_↦_`in_ {_} {_} {_} {_} {{!!}} {_} {{!!}} op' {!!} {!M!} (↓ op (V-rename wk₁ V) N)


    -- lkpᵢ op' (proj₂ (op ↓ₑ (o , i))) = just (??? , ???)


    await-promise  : {X Y : VType}
                     {o : O}
                     {i : I} →
                     (V : Γ ⊢V⦂ X) → 
                     (M : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                     -----------------------------
                     await ⟨ V ⟩ until M
                     ↝
                     M [ id-subst [ V ]ₛ ]ₘ

    -- COERCION RULES

    coerce-return  : {X : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (p : o ⊑ₒ o') →
                     (q : i ⊑ᵢ i') →
                     (V : Γ ⊢V⦂ X) →
                     --------------------------------
                     coerce p q (return V) ↝ return V

    coerce-let     : {X Y : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (p : o ⊑ₒ o') →
                     (q : i ⊑ᵢ i') →
                     (M : Γ ⊢M⦂ X ! (o , i)) →
                     (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                     ---------------------------------
                     coerce p q (let= M `in N)
                     ↝
                     let= (coerce p q M) `in (coerce p q N)

    coerce-↑       : {X : VType}
                     {o o' : O}
                     {i i' : I}
                     (p : o ⊑ₒ o') →
                     (q : i ⊑ᵢ i') →
                     {op : Σₒ} →
                     (r : op ∈ₒ o) →
                     (V : Γ ⊢V⦂ ``(arₒ op)) → 
                     (M : Γ ⊢M⦂ X ! (o , i)) →
                     -------------------------
                     coerce p q (↑ op r V M)
                     ↝
                     ↑ op (p op r) V (coerce p q M)

    coerce-promise : {X Y : VType}
                     {o o' o'' : O}
                     {i i' i'' : I}
                     (p : o ⊑ₒ o') →
                     (q : i ⊑ᵢ i') →
                     {op : Σᵢ} →
                     (r : lkpᵢ op i ≡ just (o'' , i'')) →
                     (M : Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o'' , i'')) →
                     (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
                     -------------------------------------------------------------------
                     coerce p q (promise op ∣ r ↦ M `in N)
                     ↝
                     (promise op ∣ lkpᵢ-next-eq q r ↦
                        coerce (lkpᵢ-next-⊑ₒ q r) (lkpᵢ-next-⊑ᵢ q r) M `in (coerce p q N))

    coerce-coerce  : {X : VType}
                     {o o' o'' : O}
                     {i i' i'' : I} →
                     (p : o ⊑ₒ o') →
                     (p' : o' ⊑ₒ o'') →
                     (q : i ⊑ᵢ i') →
                     (q' : i' ⊑ᵢ i'') →
                     (M : Γ ⊢M⦂ X ! (o , i)) →
                     ----------------------------------------
                     coerce p' q' (coerce p q M)
                     ↝
                     coerce (⊑ₒ-trans p p') (⊑ᵢ-trans q q') M

    -- CONTEXT RULE

    context        : {C : CType}
                     {E E' : Γ ⊢E⦂ C} →
                     E ↝ₑ E' →
                     ------------------
                     ⌈ E ⌉ ↝ ⌈ E' ⌉


  data _↝ₑ_ {Γ : Ctx} : {C : CType} → Γ ⊢E⦂ C → Γ ⊢E⦂ C → Set where

    [_]              : {X : VType}
                       {o : O}
                       {i : I}
                       {M N : Γ ⊢M⦂ X ! (o , i)} →
                       M ↝ N →
                       ---------------------------
                       [ M ] ↝ₑ [ N ]

    let=_`in_        : {X Y : VType}
                       {o : O}
                       {i : I} 
                       {E E' : Γ ⊢E⦂ X ! (o , i)} →
                       E ↝ₑ E' →
                       (N : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                       -----------------------------
                       let= E `in N ↝ₑ let= E' `in N

    ↑                : {X : VType}
                       {o : O}
                       {i : I} →
                       (op : Σₒ) →
                       (p : op ∈ₒ o) →
                       (V : Γ ⊢V⦂ ``(arₒ op)) →
                       {E E' : Γ ⊢E⦂ X ! (o , i)} →
                       E ↝ₑ E' →
                       ----------------------------
                       ↑ op p V E ↝ₑ ↑ op p V E'

    ↓                : {X : VType}
                       {o : O}
                       {i : I} →
                       (op : Σᵢ) →
                       (V : Γ ⊢V⦂ ``(arᵢ op)) →
                       {E E' : Γ ⊢E⦂ X ! (o , i)} →
                       E ↝ₑ E' →
                       ----------------------------
                       ↓ op V E ↝ₑ ↓ op V E'


    promise_∣_↦_`in_ : {X Y : VType}
                       {o o' : O}
                       {i i' : I} → 
                       (op : Σᵢ) →
                       (p : lkpᵢ op i ≡ just (o' , i')) →
                       (M : Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i')) →
                       {E E' : Γ ∷ ⟨ X ⟩ ⊢E⦂ Y ! (o , i)} →
                       E ↝ₑ E →
                       ---------------------------------
                       promise op ∣ p ↦ M `in E ↝ₑ promise op ∣ p ↦ M `in E'

    coerce           : {X : VType}
                       {o o' : O}
                       {i i' : I} →
                       (p : o ⊑ₒ o') →
                       (q : i ⊑ᵢ i') → 
                       {E E' : Γ ⊢E⦂ X ! (o , i)} →
                       E ↝ₑ E' →
                       -----------------------------
                       coerce p q E ↝ₑ coerce p q E'
 
