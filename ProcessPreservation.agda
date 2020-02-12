open import Data.List hiding ([_]) renaming (_∷_ to _::_)
open import Data.Maybe
open import Data.Product

open import Calculus
open import EffectAnnotations
open import Preservation
open import ProcessCalculus
open import ProcessTypes
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module ProcessPreservation where

-- WELL-TYPED SIGNAL HOISTING CONTEXTS

data _⊢H[_]⦂_ (Γ : Ctx) : (Δ : BCtx) → CType → Set where

  [-]              : {C : CType} →
                     -------------
                     Γ ⊢H[ [] ]⦂ C

  promise_∣_↦_`in_ : {Δ : BCtx}
                     {X Y : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (op : Σₙ) →
                     lkpᵢ op i ≡ just (o' , i') →
                     Γ ∷ ``(arₙ op) ⊢M⦂ X ! (o' , i') →
                     Γ ∷ ⟨ X ⟩ ⊢H[ Δ ]⦂ Y ! (o , i) →
                     ----------------------------------
                     Γ ⊢H[ X :: Δ ]⦂ Y ! (o , i)

  subsume          : {Δ : BCtx}
                     {X : VType}
                     {o o' : O}
                     {i i' : I} →
                     o ⊑ₒ o' →
                     i ⊑ᵢ i' → 
                     Γ ⊢H[ Δ ]⦂ X ! (o , i) →
                     ------------------------
                     Γ ⊢H[ Δ ]⦂ X ! (o' , i')


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED SIGNAL HOISTING CONTEXT

hole-ty-hₒ : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
             Γ ⊢H[ Δ ]⦂ X ! (o , i) → O
hole-ty-hₒ {_} {_} {_} {o} [-] =
  o
hole-ty-hₒ (promise op ∣ p ↦ M `in H) =
  hole-ty-hₒ H
hole-ty-hₒ (subsume p q H) =
  hole-ty-hₒ H


hole-ty-hᵢ : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
             Γ ⊢H[ Δ ]⦂ X ! (o , i) → I
hole-ty-hᵢ {_} {_} {_} {_} {o} [-] =
  o
hole-ty-hᵢ (promise op ∣ p ↦ M `in H) =
  hole-ty-hᵢ H
hole-ty-hᵢ (subsume p q H) =
  hole-ty-hᵢ H


hole-ty-h-⊑ₒ : {Γ : Ctx}
             {Δ : BCtx}
             {X : VType}
             {o : O}
             {i : I} →
             (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) →
             ------------------------------
             hole-ty-hₒ H ⊑ₒ o
hole-ty-h-⊑ₒ [-] =
  ⊑ₒ-refl
hole-ty-h-⊑ₒ (promise op ∣ p ↦ M `in H) =
  hole-ty-h-⊑ₒ H
hole-ty-h-⊑ₒ (subsume p q H) =
  ⊑ₒ-trans (hole-ty-h-⊑ₒ H) p


hole-ty-h-⊑ᵢ : {Γ : Ctx}
             {Δ : BCtx}
             {X : VType}
             {o : O}
             {i : I} →
             (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) →
             ------------------------------
             hole-ty-hᵢ H ⊑ᵢ i
hole-ty-h-⊑ᵢ [-] =
  ⊑ᵢ-refl
hole-ty-h-⊑ᵢ (promise op ∣ p ↦ M `in H) =
  hole-ty-h-⊑ᵢ H
hole-ty-h-⊑ᵢ (subsume p q H) =
  ⊑ᵢ-trans (hole-ty-h-⊑ᵢ H) q


-- FILLING A WELL-TYPED SIGNAL HOISTING CONTEXT

infix 30 _[_]ₕ

_[_]ₕ : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
        (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) → Γ ⋈ Δ ⊢M⦂ (X ! (hole-ty-hₒ H , hole-ty-hᵢ H)) →
        Γ ⊢M⦂ X ! (o , i)
[-] [ M ]ₕ =
  M
(promise op ∣ p ↦ N `in E) [ M ]ₕ =
  promise op ∣ p ↦ N `in (E [ M ]ₕ)
subsume p q E [ M ]ₕ =
  subsume p q (E [ M ]ₕ)


-- EVOLUTION OF PROCESS TYPES

infix 10 _⇝_

data _⇝_ : PType → PType → Set where

  id  : {PP : PType} →
        -------------------
        PP ⇝ PP

  ops : {PP : SkelPType}
        {o : O}
        (op : Σₙ) → 
        ----------------------------------------------
        PP ‼ o
        ⇝
        proj₁ (op ↓ₚ (PP , o)) ‼ proj₂ (op ↓ₚ (PP , o))

  par : {PP PP' QQ QQ' : SkelPType}
        {o o' o'' : O} → 
        PP ‼ o ⇝ PP' ‼ o' →
        QQ ‼ o ⇝ QQ' ‼ o'' →
        ----------------------------------------
        (PP ∥ QQ) ‼ o ⇝ (PP' ∥ QQ') ‼ (o' ∪ₒ o'')


-- EVOLUTION OF PROCESS TYPES PRESERVES SIGNAL ANNOTATIONS

⇝-⊑ₒ : {PP QQ : SkelPType}
       {o o' : O}
       {op : Σₙ} →
       PP ‼ o ⇝ QQ ‼ o' →
       op ∈ₒ o →
       -------------------
       op ∈ₒ o'
⇝-⊑ₒ id q =
  q
⇝-⊑ₒ {PP} (ops op) q =
  opₒ-in-↓ₚ PP q
⇝-⊑ₒ {_} {_} {_} {_} {op} (par p q) r with ⇝-⊑ₒ p r
... | s = ⊑ₒ-inl op s 


-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-var : {Γ : Ctx} → (Δ : BCtx) → {A : BType} → `` A ∈ Γ ⋈ Δ → `` A ∈ Γ
strengthen-var [] x = x
strengthen-var (y :: Δ) x with strengthen-var Δ x
... | Tl p = p


strengthen-val : {Γ : Ctx} {Δ : BCtx} {A : BType} → Γ ⋈ Δ ⊢V⦂ `` A → Γ ⊢V⦂ `` A
strengthen-val {_} {Δ} (` x) =
  ` strengthen-var Δ x
strengthen-val (``_ c) =
  ``_ c


-- EVALUATION CONTEXTS FOR PROCESSES

infix 10 _⊢F⦂_

data _⊢F⦂_ (Γ : Ctx) : PType → Set where

  [-]     : {PP : PType} →
            --------------
            Γ ⊢F⦂ PP

  ∥ₗ      : {PP QQ : SkelPType}
            {o : O} → 
            Γ ⊢F⦂ PP ‼ o →
            Γ ⊢P⦂ QQ ‼ o →
            --------------------
            Γ ⊢F⦂ (PP ∥ QQ) ‼ o

  ∥ᵣ      : {PP QQ : SkelPType}
            {o : O} → 
            Γ ⊢P⦂ PP ‼ o →
            Γ ⊢F⦂ QQ ‼ o →
            ------------------
            Γ ⊢F⦂ (PP ∥ QQ) ‼ o

  ↑       : {PP : SkelPType}
            {o : O} →
            (op : Σₙ) →
            op ∈ₒ o →
            Γ ⊢V⦂ ``(arₙ op) →
            Γ ⊢F⦂ PP ‼ o →
            ------------------
            Γ ⊢F⦂ PP ‼ o

  ↓       : {PP : SkelPType}
            {o : O}
            (op : Σₙ) →
            Γ ⊢V⦂ ``(arₙ op) →
            Γ ⊢F⦂ PP ‼ o →
            ----------------------------------------------------
            Γ ⊢F⦂ proj₁ (op ↓ₚ (PP , o)) ‼ proj₂ (op ↓ₚ (PP , o))

  subsume : {PP PP' : SkelPType}
            {o o' : O} → 
            PP ⊑ₚ PP' → 
            o ⊑ₒ o' → 
            Γ ⊢F⦂ PP ‼ o →
            --------------------
            Γ ⊢F⦂ PP' ‼ o'


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED PROCESS EVALUATION CONTEXT

hole-ty-f : {Γ : Ctx} {PP : PType} → Γ ⊢F⦂ PP → PType
hole-ty-f {_} {PP} [-] =
  PP
hole-ty-f (∥ₗ F Q) =
  hole-ty-f F
hole-ty-f (∥ᵣ P F) =
  hole-ty-f F
hole-ty-f (↑ op p V F) =
  hole-ty-f F
hole-ty-f (↓ op V F) =
  hole-ty-f F
hole-ty-f (subsume p q F) =
  hole-ty-f F


-- FILLING A WELL-TYPED PROCESS EVALUATION CONTEXT

infix 30 _[_]f

_[_]f : {Γ : Ctx} {PP : PType} → (F : Γ ⊢F⦂ PP) → (P : Γ ⊢P⦂ hole-ty-f F) → Γ ⊢P⦂ PP
[-] [ P ]f =
  P
(∥ₗ F Q) [ P ]f =
  (F [ P ]f) ∥ Q
(∥ᵣ Q F) [ P ]f =
  Q ∥ (F [ P ]f)
(↑ op p V F) [ P ]f =
  ↑ op p V (F [ P ]f)
(↓ op V F) [ P ]f =
  ↓ op V (F [ P ]f)
(subsume p q F) [ P ]f =
  subsume p q (F [ P ]f)


-- PROCESS EVALUATION CONTEXT TYPE EVOLUTION

⇝-f-ty : {Γ : Ctx} {PP QQ : PType} → (F : Γ ⊢F⦂ PP) → hole-ty-f F ⇝ QQ → Σ[ RR ∈ PType ] (PP ⇝ RR)
⇝-f-ty {_} {_} {QQ} [-] p =
  QQ , p
⇝-f-ty (∥ₗ {_} {QQ} {o} F Q) p with ⇝-f-ty F p
... | ((RR ‼ o') , r) =
  ((RR ∥ QQ) ‼ (o' ∪ₒ o)) , par r id
⇝-f-ty (∥ᵣ {PP} {_} {o} P F) p with ⇝-f-ty F p 
... | ((RR ‼ o') , r) =
  ((PP ∥ RR) ‼ (o ∪ₒ o')) , par id r
⇝-f-ty (↑ op p V F) q = {!!}
⇝-f-ty (↓ op V F) p = {!!}
⇝-f-ty (subsume p q F) r = {!!}


{-
⇝-f : {Γ : Ctx} {PP QQ : PType} → (F : Γ ⊢F⦂ PP) → hole-ty-f F ⇝ QQ → Σ[ RR ∈ PType ] (Γ ⊢F⦂ RR)
⇝-f {_} {_} {QQ} [-] p =
  QQ , [-]
⇝-f (∥ₗ {_} {QQ'} {o''} F Q) p with ⇝-f F p
... | (PP' ‼ o') , F' =
  ((PP' ∥ QQ') ‼ (o' ∪ₒ o'')) , ∥ₗ (subsume ⊑ₚ-refl ⊑ₒ-inl F') (subsume ⊑ₚ-refl ⊑ₒ-inr Q)
⇝-f (∥ᵣ {PP'} {_} {o'}  P F) p with ⇝-f F p
... | (QQ' ‼ o'') , F' =
  ((PP' ∥ QQ') ‼ (o' ∪ₒ o'')) , ∥ᵣ (subsume ⊑ₚ-refl ⊑ₒ-inl P) (subsume ⊑ₚ-refl ⊑ₒ-inr F')
⇝-f (↑ op p V F) q with ⇝-f F q
... | (QQ' ‼ o') , F' =
  (QQ' ‼ {!!}) , ↑ op {!!} V F'
⇝-f (↓ op V F) p =
  {!!}
⇝-f (subsume p q F) r =
  {!!}
-}
  
-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED PROCESSES
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

infix 10 _[_]↝_

data _[_]↝_ {Γ : Ctx} : {PP : PType} → Γ ⊢P⦂ PP → {QQ : PType} → PP ⇝ QQ → Γ ⊢P⦂ QQ → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run   : {X : VType}
          {o : O}
          {i : I}
          {M N : Γ ⊢M⦂ X ! (o , i)} → 
          M ↝ N →
          ---------------------------
          (run M) [ id ]↝ (run N)

  -- BROADCAST RULES

  bcastₗ : {PP QQ : SkelPType}
           {o : O}
           {op : Σₙ} → 
           (p : op ∈ₒ o) →
           (V : Γ ⊢V⦂ `` (arₙ op)) →
           (P : Γ ⊢P⦂ PP ‼ o) →
           (Q : Γ ⊢P⦂ QQ ‼ o) →
           ------------------------------------------
           (↑ op p V P ∥ Q)
           [ par id (ops op) ]↝
           (↑ op (⊑ₒ-inl op p)
                 V
                 (subsume ⊑ₚ-refl ⊑ₒ-inl P
                  ∥
                  subsume ⊑ₚ-refl ⊑ₒ-inr (↓ op V Q)))

  bcastᵣ : {PP QQ : SkelPType}
           {o : O}
           {op : Σₙ} → 
           (p : op ∈ₒ o) →
           (V : Γ ⊢V⦂ `` (arₙ op)) →
           (P : Γ ⊢P⦂ PP ‼ o) →
           (Q : Γ ⊢P⦂ QQ ‼ o) →
           ----------------------------------------
           (P ∥ ↑ op p V Q)
           [ par (ops op) id ]↝
           (↑ op (⊑ₒ-inr op p)
                 V
                 (subsume ⊑ₚ-refl ⊑ₒ-inl (↓ op V P)
                  ∥
                  subsume ⊑ₚ-refl ⊑ₒ-inr Q))

  -- INTERRUPT RULES

  ↓-run : {X : VType}
          {o : O}
          {i : I}
          {op : Σₙ} → 
          (V : Γ ⊢V⦂ `` (arₙ op)) → 
          (M : Γ ⊢M⦂ X ! (o , i)) →
          -------------------------
          ↓ op V (run M)
          [ id ]↝
          run (↓ op V M)

  ↓-par : {PP QQ : SkelPType}
          {o : O}
          {op : Σₙ}
          (V : Γ ⊢V⦂ `` (arₙ op)) →
          (P : Γ ⊢P⦂ PP ‼ o) →
          (Q : Γ ⊢P⦂ QQ ‼ o) →
          ----------------------------------------------------------------------
          ↓ op V (P ∥ Q)
          [ id ]↝
          (subsume ⊑ₚ-refl ⊑ₒ-inl (↓ op V P) ∥ subsume ⊑ₚ-refl ⊑ₒ-inr (↓ op V Q))

  ↓-↑   : {PP : SkelPType}
          {o : O}
          {op : Σₙ}
          {op' : Σₙ} →
          (p : op' ∈ₒ o) →
          (V : Γ ⊢V⦂ ``(arₙ op)) →
          (W : Γ ⊢V⦂ ``(arₙ op')) →
          (P : Γ ⊢P⦂ PP ‼ o) →
          -----------------------------------
          ↓ op V (↑ op' p W P)
          [ id ]↝
          ↑ op' (opₒ-in-↓ₚ PP p) W (↓ op V P)

  -- HOISTING RULE

  ↑     : {Δ : BCtx}
          {X : VType}
          {o o' : O}
          {i i' : I} → 
          (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) → 
          {op : Σₙ} → 
          (p : op ∈ₒ hole-ty-hₒ H) →
          (V : Γ ⋈ Δ ⊢V⦂ `` (arₙ op)) →
          (M : Γ ⋈ Δ ⊢M⦂ X ! (hole-ty-hₒ H , hole-ty-hᵢ H)) →
          ----------------------------------------------------------------------
          (run (H [ ↑ op p V M ]ₕ))
          [ id ]↝
          (↑ op (hole-ty-h-⊑ₒ H op p) (strengthen-val {Δ = Δ} V) (run (H [ M ]ₕ)))

  -- CONTEXT RULE

  context : {PP QQ : PType}
            {F : Γ ⊢F⦂ PP}
            {P : Γ ⊢P⦂ hole-ty-f F}
            {Q : Γ ⊢P⦂ QQ}
            {p : hole-ty-f F ⇝ QQ} →
            P [ p ]↝ Q →
            ---------------
            {!!} [ {!!} ]↝ {!!}

  -- SUBSUMPTION RULES

  subsume-run     : {X : VType}
                    {o o' : O}
                    {i i' : I}
                    {p : o ⊑ₒ o'}
                    {q : i ⊑ᵢ i'} → 
                    (M : Γ ⊢M⦂ X ! (o , i)) →
                    -----------------------------
                    subsume (sub-run q) p (run M)
                    [ id ]↝
                    run (subsume p q M)

  subume-∥        : {PP PP' QQ QQ' : SkelPType}
                    {o o' : O}
                    {p : PP ⊑ₚ PP'}
                    {q : QQ ⊑ₚ QQ'}
                    {r : o ⊑ₒ o'} → 
                    (P : Γ ⊢P⦂ PP ‼ o) →
                    (Q : Γ ⊢P⦂ QQ ‼ o) → 
                    --------------------------------
                    subsume (sub-par p q) r (P ∥ Q)
                    [ id ]↝
                    (subsume p r P) ∥ (subsume q r Q)

  subsume-↑       : {PP PP' : SkelPType}
                    {o o' : O}
                    {op : Σₙ}
                    {p : PP ⊑ₚ PP'}
                    {q : o ⊑ₒ o'} → 
                    (r : op ∈ₒ o) →
                    (V : Γ ⊢V⦂ ``(arₙ op)) →
                    (P : Γ ⊢P⦂ PP ‼ o) →
                    -------------------------------
                    subsume p q (↑ op r V P)
                    [ id ]↝
                    ↑ op (q op r) V (subsume p q P)

  subsume-subsume : {PP PP' PP'' : SkelPType}
                    {o o' o'' : O}
                    {p : PP ⊑ₚ PP'}
                    {p' : PP' ⊑ₚ PP''}
                    {q : o ⊑ₒ o'}
                    {q' : o' ⊑ₒ o''}
                    (P : Γ ⊢P⦂ PP ‼ o) →
                    -----------------------------------------
                    subsume p' q' (subsume p q P)
                    [ id ]↝
                    subsume (⊑ₚ-trans p p') (⊑ₒ-trans q q') P

