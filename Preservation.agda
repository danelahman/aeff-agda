open import Data.Maybe
open import Data.Product
open import Data.List hiding ([_]) renaming (_∷_ to _::_)

open import Calculus
open import EffectAnnotations
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module Preservation where

-- EVALUATION CONTEXTS

BCtx = List VType

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
                     (op : Σₒ) →
                     op ∈ₒ o →
                     Γ ⊢V⦂ ``(arₒ op) →
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     ------------------------
                     Γ ⊢E[ Δ ]⦂ X ! (o , i)

  ↓                : {Δ : BCtx}
                     {X : VType}
                     {o : O}
                     {i : I}
                     (op : Σᵢ) →
                     Γ ⊢V⦂ ``(arᵢ op) →
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     ---------------------------
                     Γ ⊢E[ Δ ]⦂ X ! op ↓ₑ (o , i)

  promise_∣_↦_`in_ : {Δ : BCtx}
                     {X Y : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (op : Σᵢ) →
                     lkpᵢ op i ≡ just (o' , i') →
                     Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i') →
                     Γ ∷ ⟨ X ⟩ ⊢E[ Δ ]⦂ Y ! (o , i) →
                     ----------------------------------
                     Γ ⊢E[ ⟨ X ⟩ :: Δ ]⦂ Y ! (o , i)

  coerce           : {Δ : BCtx}
                     {X : VType}
                     {o o' : O}
                     {i i' : I} →
                     o ⊑ₒ o' →
                     i ⊑ᵢ i' → 
                     Γ ⊢E[ Δ ]⦂ X ! (o , i) →
                     ------------------------
                     Γ ⊢E[ Δ ]⦂ X ! (o' , i')


-- MERGING AN ORDINARY AND A BINDING CONTEXT

infix 30 _⋈_

_⋈_ : Ctx → BCtx → Ctx
Γ ⋈ [] = Γ
Γ ⋈ (X :: Δ) = (Γ ∷ X) ⋈ Δ


-- FINDING THE TYPE OF THE HOLE OF AN EVALUATION CONTEXT

hole-ty : {Γ : Ctx} {Δ : BCtx} {C : CType} → Γ ⊢E[ Δ ]⦂ C → CType
hole-ty {_} {_} {C} [-] = C
hole-ty (let= E `in M) = hole-ty E
hole-ty (↑ op p V E) = hole-ty E
hole-ty (↓ op V E) = hole-ty E
hole-ty (promise op ∣ p ↦ M `in E) = hole-ty E
hole-ty (coerce p q E) = hole-ty E


-- FILLING AN EVALUATION CONTEXT

infix 30 _[_]

_[_] : {Γ : Ctx} {Δ : BCtx} {C : CType} → (E : Γ ⊢E[ Δ ]⦂ C) → Γ ⋈ Δ ⊢M⦂ (hole-ty E) → Γ ⊢M⦂ C
[-] [ M ] = M
(let= E `in N) [ M ] = let= (E [ M ]) `in N
↑ op p V E [ M ] = ↑ op p V (E [ M ])
↓ op V E [ M ] = ↓ op V (E [ M ])
(promise op ∣ p ↦ N `in E) [ M ] = promise op ∣ p ↦ N `in (E [ M ])
coerce p q E [ M ] = coerce p q (E [ M ])


-- SMALL-STEP OPERATIONAL SEMANTICS FOR COMPUTATIONS
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

mutual

  infix 10 _↝_

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
                     ---------------------------------------------------------------------------------------
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

    await-promise  : {X Y : VType}
                     {o : O}
                     {i : I} →
                     (V : Γ ⊢V⦂ X) → 
                     (M : Γ ∷ X ⊢M⦂ Y ! (o , i)) →
                     -----------------------------
                     await ⟨ V ⟩ until M
                     ↝
                     M [ id-subst [ V ]ₛ ]ₘ

    -- COERCION/SUBSUMPTION RULES

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
                     ---------------------------------------
                     coerce p' q' (coerce p q M)
                     ↝
                     coerce (⊑ₒ-trans p p') (⊑ᵢ-trans q q') M


  -- EVALUATION CONTEXT RULE

    context        : {Δ : BCtx}
                     {C : CType}
                     {E : Γ ⊢E[ Δ ]⦂ C} →
                     {M N : Γ ⋈ Δ ⊢M⦂ (hole-ty E)} →
                     M ↝ N →
                     -------------------------------
                     E [ M ] ↝ E [ N ]
