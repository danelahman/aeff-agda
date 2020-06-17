open import Data.Empty
open import Data.List renaming (_∷_ to _∷ₗ_ ; [_] to [_]ₗ)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
open import AwaitingComputations
open import EffectAnnotations
open import Finality
open import Preservation
open import ProcessPreservation
open import ProcessProgress
open import Progress
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module ProcessFinality where

-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED PROCESSES
-- WITH INLINED EVALUATION CONTEXT RULES

infix 10 _[_]↝↝_

data _[_]↝↝_ {Γ : Ctx} : {o o' : O} {PP : PType o} {QQ : PType o'} → Γ ⊢P⦂ PP → PP ⇝ QQ → Γ ⊢P⦂ QQ → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run   : {X : VType}
          {o : O}
          {i : I}
          {M N : Γ ⊢M⦂ X ! (o , i)} → 
          M ↝↝ N →
          ---------------------------
          (run M) [ id ]↝↝ (run N)

  -- BROADCAST RULES

  ↑-∥ₗ   : {o o' : O}
           {PP : PType o}
           {QQ : PType o'}
           {op : Σₛ} → 
           (p : op ∈ₒ o) →
           (V : Γ ⊢V⦂ `` (payload op)) →
           (P : Γ ⊢P⦂ PP) →
           (Q : Γ ⊢P⦂ QQ) →
           ------------------------------------------
           ((↑ op p V P) ∥ Q)
           [ par ⇝-refl (⇝-↓ {op = op}) ]↝↝
           ↑ op (∪ₒ-inl op p) V (P ∥ ↓ op V Q)

  ↑-∥ᵣ   : {o o' : O}
           {PP : PType o}
           {QQ : PType o'}
           {op : Σₛ} → 
           (p : op ∈ₒ o') →
           (V : Γ ⊢V⦂ `` (payload op)) →
           (P : Γ ⊢P⦂ PP) →
           (Q : Γ ⊢P⦂ QQ) →
           ------------------------------------------
           (P ∥ (↑ op p V Q))
           [ par (⇝-↓ {op = op}) ⇝-refl ]↝↝
           ↑ op (∪ₒ-inr op p) V (↓ op V P ∥ Q)

  -- INTERRUPT PROPAGATION RULES

  ↓-run : {X : VType}
          {o : O}
          {i : I}
          {op : Σₛ} → 
          (V : Γ ⊢V⦂ `` (payload op)) → 
          (M : Γ ⊢M⦂ X ! (o , i)) →
          -----------------------------
          ↓ op V (run M)
          [ id ]↝↝
          run (↓ op V M)

  ↓-∥   : {o o' : O}
          {PP : PType o}
          {QQ : PType o'}
          {op : Σₛ}
          (V : Γ ⊢V⦂ `` (payload op)) →
          (P : Γ ⊢P⦂ PP) →
          (Q : Γ ⊢P⦂ QQ) →
          -----------------------------
          ↓ op V (P ∥ Q)
          [ ⇝-refl ]↝↝
          ((↓ op V P) ∥ (↓ op V Q))

  ↓-↑   : {o : O}
          {PP : PType o}
          {op : Σₛ}
          {op' : Σₛ} →
          (p : op' ∈ₒ o) →
          (V : Γ ⊢V⦂ ``(payload op)) →
          (W : Γ ⊢V⦂ ``(payload op')) →
          (P : Γ ⊢P⦂ PP) →
          -----------------------------------
          ↓ op V (↑ op' p W P)
          [ ⇝-refl ]↝↝
          ↑ op' (↓ₚ-⊑ₒ PP op' p) W (↓ op V P)

  -- SIGNAL HOISTING RULE

  ↑     : {X : VType}
          {o : O}
          {i : I} → 
          {op : Σₛ} → 
          (p : op ∈ₒ o) →
          (V : Γ ⊢V⦂ `` (payload op)) →
          (M : Γ ⊢M⦂ X ! (o , i)) →
          -----------------------------
          run (↑ op p V M)
          [ id ]↝↝
          ↑ op p V (run M)

  -- EVALUATION CONTEXT RULES

  context-∥ₗ : {o o' o'' : O}
               {PP : PType o}
               {PP' : PType o''}
               {QQ : PType o'}
               {P : Γ ⊢P⦂ PP}
               {P' : Γ ⊢P⦂ PP'}
               {Q : Γ ⊢P⦂ QQ}
               {p : PP ⇝ PP'} → 
               P [ p ]↝↝ P' → 
               ------------------
               P ∥ Q
               [ par p ⇝-refl ]↝↝
               P' ∥ Q

  context-∥ᵣ : {o o' o'' : O}
               {PP : PType o}
               {QQ : PType o'}
               {QQ' : PType o''}
               {P : Γ ⊢P⦂ PP}
               {Q : Γ ⊢P⦂ QQ}
               {Q' : Γ ⊢P⦂ QQ'}
               {r : QQ ⇝ QQ'} → 
               Q [ r ]↝↝ Q' → 
               ------------------
               P ∥ Q
               [ par ⇝-refl r ]↝↝
               P ∥ Q'

  context-↑ : {o o' : O}
              {PP : PType o}
              {PP' : PType o'}
              {op : Σₛ}
              {p : op ∈ₒ o} →
              {V : Γ ⊢V⦂ ``(payload op)}
              {P : Γ ⊢P⦂ PP}
              {P' : Γ ⊢P⦂ PP'}
              {r : PP ⇝ PP'} → 
              P [ r ]↝↝ P' →
              --------------------------
              ↑ op p V P
              [ r ]↝↝
              ↑ op (⇝-↓ₚ-⊑ₒ r op p) V P'

  context-↓ : {o o' : O}
              {PP : PType o}
              {PP' : PType o'}
              {op : Σₛ}
              {V : Γ ⊢V⦂ ``(payload op)}
              {P : Γ ⊢P⦂ PP}
              {P' : Γ ⊢P⦂ PP'}
              {r : PP ⇝ PP'} →
              P [ r ]↝↝ P' →
              ----------------------
              ↓ op V P
              [ ⇝-↓ₚ r ]↝↝
              ↓ op V P'


-- ONE-TO-ONE CORRESPONDENCE BETWEEN THE TWO SETS OF REDUCTION RULES

[]↝↝-to-[]↝ : {Γ : Ctx}
              {o o' : O}
              {PP : PType o}
              {QQ : PType o'}
              {P : Γ ⊢P⦂ PP}
              {Q : Γ ⊢P⦂ QQ}
              {r : PP ⇝ QQ} → 
              P [ r ]↝↝ Q →
              -----------------
              P [ r ]↝ Q

[]↝↝-to-[]↝ (run r) =
  run (↝↝-to-↝ r)
[]↝↝-to-[]↝ (↑-∥ₗ p V P Q) =
  ↑-∥ₗ p V P Q
[]↝↝-to-[]↝ (↑-∥ᵣ p V P Q) =
  ↑-∥ᵣ p V P Q
[]↝↝-to-[]↝ (↓-run V M) =
  ↓-run V M
[]↝↝-to-[]↝ (↓-∥ V P Q) =
  ↓-∥ V P Q
[]↝↝-to-[]↝ (↓-↑ p V W P) =
  ↓-↑ p V W P
[]↝↝-to-[]↝ (↑ p V M) =
  ↑ p V M
[]↝↝-to-[]↝ (context-∥ₗ r) =
  context (_ ∥ₗ _) ([]↝↝-to-[]↝ r)
[]↝↝-to-[]↝ (context-∥ᵣ r) =
  context (_ ∥ᵣ _) ([]↝↝-to-[]↝ r)
[]↝↝-to-[]↝ (context-↑ r) =
  context (↑ _ _ _ _) ([]↝↝-to-[]↝ r)
[]↝↝-to-[]↝ (context-↓ r) =
  context (↓ _ _ _) ([]↝↝-to-[]↝ r)


≡-app₂ : {X Y Z : Set}
         {f g : X → Y → Z} →
         f ≡ g →
         (x : X) →
         (y : Y) → 
         ---------------
         f x y ≡ g x y
        
≡-app₂ refl x y =
  refl

postulate
  []↝-context-to-[]↝↝-aux : {Γ : Ctx}
                          {o o' : O}
                          {op : Σₛ}
                          {p : op ∈ₒ o}
                          {PP : PType o}
                          {QQ : PType o'} → 
                          (F : Γ ⊢F⦂ PP) →
                          (r : proj₂ (hole-ty-f F) ⇝ QQ) →
                          ----------------------------------------------------------
                          ⇝-↓ₚ-⊑ₒ (proj₂ (proj₂ (⇝-f-⇝ F r))) op p ≡ ⇝-f-∈ₒ F r op p

--[]↝-context-to-[]↝↝-aux {Γ} {o} {o'} {op} {p} F r =
--  ≡-app₂ (⊑ₒ-irrelevant (⇝-↓ₚ-⊑ₒ (proj₂ (proj₂ (⇝-f-⇝ F r)))) (⇝-f-∈ₒ F r)) op p

{-

  Agda bug?

  We have

  ⊑ₒ-irrelevant (⇝-↓ₚ-⊑ₒ (proj₂ (proj₂ (⇝-f-⇝ F r)))) (⇝-f-∈ₒ F r) 

    : ⇝-↓ₚ-⊑ₒ (proj₂ (proj₂ (⇝-f-⇝ F r))) ≡ ⇝-f-∈ₒ F r

  But typechecking

    ≡-app₂ (⊑ₒ-irrelevant (⇝-↓ₚ-⊑ₒ (proj₂ (proj₂ (⇝-f-⇝ F r)))) (⇝-f-∈ₒ F r)) op p

  gives the following error:

  Cannot instantiate the metavariable _1131 to solution op₁ ∈ₒ o
  since it contains the variable op₁
  which is not in scope of the metavariable
  when checking that the expression
  ⊑ₒ-irrelevant {p = ⇝-↓ₚ-⊑ₒ (proj₂ (proj₂ (⇝-f-⇝ F r)))} {q = ⇝-f-∈ₒ F r} 
  has type _f_1133 ≡ _g_1134

-}

mutual

  []↝-context-to-[]↝↝ : {Γ : Ctx}
                        {o o' : O}
                        {PP : PType o}
                        {QQ : PType o'} →
                        (F : Γ ⊢F⦂ PP) → 
                        {P : Γ ⊢P⦂ proj₂ (hole-ty-f F)}
                        {Q : Γ ⊢P⦂ QQ}
                        {r : proj₂ (hole-ty-f F) ⇝ QQ} → 
                        P [ r ]↝ Q →
                        -----------------------------------------------------------------------------
                        F [ P ]f
                        [ proj₂ (proj₂ (⇝-f-⇝ F r)) ]↝↝
                        (⇝-f F r) [ subst-i PType (λ o QQ → Γ ⊢P⦂ QQ) (⇝-f-tyₒ F r) (⇝-f-ty F r) Q ]f

  []↝-context-to-[]↝↝ [-] r =
    []↝-to-[]↝↝ r
  []↝-context-to-[]↝↝ (F ∥ₗ Q) r =
    context-∥ₗ ([]↝-context-to-[]↝↝ F r)
  []↝-context-to-[]↝↝ (P ∥ᵣ F) r =
    context-∥ᵣ ([]↝-context-to-[]↝↝ F r)
  []↝-context-to-[]↝↝ {Γ} {o} {o'} {PP} {QQ} (↑ op p V F) {P} {Q} {r'} r
    rewrite sym ([]↝-context-to-[]↝↝-aux {op = op} {p = p} F r') =
      context-↑ ([]↝-context-to-[]↝↝ F r)
  []↝-context-to-[]↝↝ (↓ op V F) r =
    context-↓ ([]↝-context-to-[]↝↝ F r)


  []↝-to-[]↝↝ : {Γ : Ctx}
                {o o' : O}
                {PP : PType o}
                {QQ : PType o'}
                {P : Γ ⊢P⦂ PP}
                {Q : Γ ⊢P⦂ QQ}
                {r : PP ⇝ QQ} → 
                P [ r ]↝ Q →
                -----------------
                P [ r ]↝↝ Q

  []↝-to-[]↝↝ (run r) =
    run (↝-to-↝↝ r)
  []↝-to-[]↝↝ (↑-∥ₗ p V P Q) =
    ↑-∥ₗ p V P Q
  []↝-to-[]↝↝ (↑-∥ᵣ p V P Q) =
    ↑-∥ᵣ p V P Q
  []↝-to-[]↝↝ (↓-run V M) =
    ↓-run V M
  []↝-to-[]↝↝ (↓-∥ V P Q) =
    ↓-∥ V P Q
  []↝-to-[]↝↝ (↓-↑ p V W P) =
    ↓-↑ p V W P
  []↝-to-[]↝↝ (↑ p V M) =
    ↑ p V M
  []↝-to-[]↝↝ (context F r) =
    []↝-context-to-[]↝↝ _ r


-- FINALITY OF RESULT FORMS

par-finality-↝↝ : {o o' : O}
                  {PP : PType o}
                  {QQ : PType o'}
                  {P : [] ⊢P⦂ PP} → 
                  {Q : [] ⊢P⦂ QQ} → 
                  ParResult⟨ P ⟩ →
                  (r : PP ⇝ QQ) →
                  P [ r ]↝↝ Q →
                  -----------------
                  ⊥

par-finality-↝↝ (run R) .id (run r) =
  run-finality-↝↝ R r 
par-finality-↝↝ (run R) .id (↑ p V M) =
  run-↑-⊥ R
par-finality-↝↝ (par R S) .(par _ ⇝-refl) (context-∥ₗ r') =
  par-finality-↝↝ R _ r'
par-finality-↝↝ (par R S) .(par ⇝-refl _) (context-∥ᵣ r') =
  par-finality-↝↝ S _ r'


proc-finality-↝↝ : {o o' : O}
                  {PP : PType o}
                  {QQ : PType o'}
                  {P : [] ⊢P⦂ PP} → 
                  {Q : [] ⊢P⦂ QQ} → 
                  ProcResult⟨ P ⟩ →
                  (r : PP ⇝ QQ) →
                  P [ r ]↝↝ Q →
                  -----------------
                  ⊥

proc-finality-↝↝ (proc R) r r' =
  par-finality-↝↝ R r r'
proc-finality-↝↝ (signal R) r (context-↑ r') =
  proc-finality-↝↝ R r r'


{- LEMMA 4.2 -}

proc-finality : {o o' : O}
                {PP : PType o}
                {QQ : PType o'}
                {P : [] ⊢P⦂ PP} → 
                {Q : [] ⊢P⦂ QQ} → 
                ProcResult⟨ P ⟩ →
                (r : PP ⇝ QQ) →
                P [ r ]↝ Q →
                -----------------
                ⊥

proc-finality R r r' =
  proc-finality-↝↝ R r ([]↝-to-[]↝↝ r')
