open import Data.List renaming (_∷_ to _∷ₗ_ ; [_] to [_]ₗ)
open import Data.Maybe
open import Data.Product
open import Data.Sum

open import AEff
open import EffectAnnotations
open import Preservation
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module ProcessPreservation where

-- REDUCTION OF PROCESS TYPES

infix 10 _⇝_

data _⇝_ : {o o' : O} → PType o → PType o' → Set where

  id  : {X : VType}
        {o : O}
        {i : I} → 
        ----------------------
        X ‼ o , i ⇝ X ‼ o , i

  act : {X : VType}
        {o o' o'' : O}
        {i i' i'' : I} →
        (ops : List Σₛ) →
        (op : Σₛ) →   
        (o' , i') ≡ ops ↓↓ₑ (o , i) →
        (o'' , i'') ≡ ((ops ++ [ op ]ₗ) ↓↓ₑ (o , i)) → 
        ----------------------------------------------
        (X ‼ o' , i') ⇝ (X ‼ o'' , i'')

  par : {o o' o'' o''' : O}
        {PP : PType o}
        {QQ : PType o'}
        {PP' : PType o''}
        {QQ' : PType o'''} → 
        PP ⇝ PP' →
        QQ ⇝ QQ' →
        ----------------------
        (PP ∥ QQ) ⇝ (PP' ∥ QQ')


-- REDUCTION OF PROCESS TYPES IS REFLEXIVE

{- LEMMA 4.4 (1) -}

⇝-refl : {o : O} {PP : PType o} → PP ⇝ PP
⇝-refl {o} {X ‼ o , i} =
  id
⇝-refl {.(_ ∪ₒ _)} {PP ∥ QQ} =
  par ⇝-refl ⇝-refl


-- ACTION OF INTERRUPTS ON GENERAL PROCESS TYPES IS A REDUCTION

{- LEMMA 4.4 (2) -}

⇝-↓ₚ : {o : O}
       {PP : PType o}
       {op : Σₛ} →
       --------------
       PP ⇝ op ↓ₚ PP

⇝-↓ₚ {.o} {X ‼ o , i} {op} =
  act [] op refl refl
⇝-↓ₚ {.(_ ∪ₒ _)} {PP ∥ QQ} {op} =
  par ⇝-↓ₚ ⇝-↓ₚ


-- ACTION OF INTERRUPTS PRESERVES PROCESS TYPE REDUCTION

{- LEMMA 4.4 (3) -}

⇝-↓ₚ-cong : {o o' : O}
            {PP : PType o}
            {QQ : PType o'}
            {op : Σₛ} →
            PP ⇝ QQ → 
            --------------------
            op ↓ₚ PP ⇝ op ↓ₚ QQ

⇝-↓ₚ-cong id =
  id
⇝-↓ₚ-cong {_} {_} {_} {_} {op} (act {_} {o} {o'} {o''} {i} {i'} {i''} ops op' p q) =
  act {o = o} {i = i} (op ∷ₗ ops) op' (cong (λ oi → op ↓ₑ oi) p) (cong (λ oi → op ↓ₑ oi) q) 
⇝-↓ₚ-cong (par p q) =
  par (⇝-↓ₚ-cong p) (⇝-↓ₚ-cong q)


-- PROCESS TYPE REDUCTION INCREASES SIGNAL INDEX

{- LEMMA 4.4 (4) -}

inj-proj₁ : {X Y : Set} {xy xy' : X × Y} → xy ≡ xy' → proj₁ xy ≡ proj₁ xy'
inj-proj₁ refl = refl

⇝-⊑ₒ : {o o' : O}
       {PP : PType o}
       {QQ : PType o'} →
       PP ⇝ QQ →
       ------------------
       o ⊑ₒ o'

⇝-⊑ₒ id =
  ⊑ₒ-refl
⇝-⊑ₒ (act {_} {o} {o'} {o''} {i} ops op p q) with inj-proj₁ p | inj-proj₁ q
... | r | s = 
  subst (λ o → o ⊑ₒ o'')
        (sym r)
        (subst (λ o'' → proj₁ (ops ↓↓ₑ (o , i)) ⊑ₒ o'')
               (sym s)
               (subst (λ v → proj₁ (ops ↓↓ₑ (o , i)) ⊑ₒ proj₁ v)
                      (sym (↓↓ₑ-act ops [ op ]ₗ))
                      (↓↓ₑ-⊑ₒ-act ops op)))
⇝-⊑ₒ (par p q) =
  ∪ₒ-fun (⇝-⊑ₒ p) (⇝-⊑ₒ q)


-- EVALUATION CONTEXTS FOR PROCESSES

infix 10 _⊢F⦂_

data _⊢F⦂_ (Γ : Ctx) : {o : O} → PType o → Set where

  [-]     : {o : O} → 
            {PP : PType o} →
            --------------
            Γ ⊢F⦂ PP

  _∥ₗ_    : {o o' : O}
            {PP : PType o}
            {QQ : PType o'} → 
            Γ ⊢F⦂ PP →
            Γ ⊢P⦂ QQ →
            ------------------
            Γ ⊢F⦂ (PP ∥ QQ)

  _∥ᵣ_    : {o o' : O}
            {PP : PType o}
            {QQ : PType o'} →
            Γ ⊢P⦂ PP →
            Γ ⊢F⦂ QQ →
            ------------------
            Γ ⊢F⦂ (PP ∥ QQ)

  ↑       : {o : O}
            {PP : PType o}  →
            (op : Σₛ) →
            op ∈ₒ o →
            Γ ⊢V⦂ ``(payload op) →
            Γ ⊢F⦂ PP →
            ----------------------
            Γ ⊢F⦂ PP

  ↓       : {o : O}
            {PP : PType o}
            (op : Σₛ) →
            Γ ⊢V⦂ ``(payload op) →
            Γ ⊢F⦂ PP →
            ----------------------
            Γ ⊢F⦂ op ↓ₚ PP
            

-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED PROCESS EVALUATION CONTEXT

hole-ty-f : {Γ : Ctx} {o : O} {PP : PType o} → Γ ⊢F⦂ PP → Σ[ o' ∈ O ] (PType o')
hole-ty-f {_} {o} {PP} [-] =
  o , PP
hole-ty-f (_∥ₗ_ {o} {o'} {PP} {QQ} F Q) =
  proj₁ (hole-ty-f F) , proj₂ (hole-ty-f F)
hole-ty-f (_∥ᵣ_ {o} {o'} {PP} {QQ} P F) =
  proj₁ (hole-ty-f F) , proj₂ (hole-ty-f F)
hole-ty-f (↑ op p V F) =
  proj₁ (hole-ty-f F) , proj₂ (hole-ty-f F)
hole-ty-f (↓ op V F) =
  proj₁ (hole-ty-f F) , proj₂ (hole-ty-f F)


-- FILLING A WELL-TYPED PROCESS EVALUATION CONTEXT

infix 30 _[_]f

_[_]f : {Γ : Ctx} {o : O} {PP : PType o} → (F : Γ ⊢F⦂ PP) → (P : Γ ⊢P⦂ proj₂ (hole-ty-f F)) → Γ ⊢P⦂ PP
[-] [ P ]f =
  P
(F ∥ₗ Q) [ P ]f =
  (F [ P ]f) ∥ Q
(Q ∥ᵣ F) [ P ]f =
  Q ∥ (F [ P ]f)
(↑ op p V F) [ P ]f =
  ↑ op p V (F [ P ]f)
(↓ op V F) [ P ]f =
  ↓ op V (F [ P ]f)


-- TYPES OF WELL-TYPED PROCESS EVALUATION CONTEXTS ALSO REDUCE

⇝-f-⇝ : {Γ : Ctx}
        {o o' : O}
        {PP : PType o}
        {QQ : PType o'} →
        (F : Γ ⊢F⦂ PP) →
        proj₂ (hole-ty-f F) ⇝ QQ →
        ------------------------------------------
        Σ[ o'' ∈ O ] Σ[ RR ∈ PType o'' ] (PP ⇝ RR)

⇝-f-⇝ {_} {_} {o'} {_} {QQ} [-] p =
  o' , QQ , p
⇝-f-⇝ (_∥ₗ_ {o} {o'} {PP} {QQ} F Q) p with ⇝-f-⇝ F p
... | o'' , RR , q =
  (o'' ∪ₒ o') , (RR ∥ QQ) , par q ⇝-refl
⇝-f-⇝ (_∥ᵣ_ {o} {o'} {PP} {QQ} P F) p with ⇝-f-⇝ F p
... | o'' , RR , q =
  (o ∪ₒ o'') , (PP ∥ RR) , par ⇝-refl q
⇝-f-⇝ (↑ op p V F) q with ⇝-f-⇝ F q
... | o'' , RR , r =
  o'' , RR , r
⇝-f-⇝ (↓ op V F) p with ⇝-f-⇝ F p
... | o'' , RR , q =
  proj₁ (op ↓ₚₚ RR) , (op ↓ₚ RR) , ⇝-↓ₚ-cong q


⇝-f-∈ₒ : {Γ : Ctx}
         {o o' : O}
         {PP : PType o}
         {QQ : PType o'}
         (F : Γ ⊢F⦂ PP) →
         (p : proj₂ (hole-ty-f F) ⇝ QQ) →
         --------------------------------
         o ⊑ₒ proj₁ (⇝-f-⇝ F p)

⇝-f-∈ₒ [-] p =
  ⇝-⊑ₒ p
⇝-f-∈ₒ (F ∥ₗ Q) p =
  ∪ₒ-fun (⇝-f-∈ₒ F p) ⊑ₒ-refl
⇝-f-∈ₒ (P ∥ᵣ F) p =
  ∪ₒ-fun ⊑ₒ-refl (⇝-f-∈ₒ F p)
⇝-f-∈ₒ (↑ op p V F) q =
  ⇝-f-∈ₒ F q
⇝-f-∈ₒ (↓ {o} {PP} op V F) p =
  ⇝-f-∈ₒ-aux (⇝-f-⇝ F p) refl

  where
    ⇝-f-∈ₒ-aux : (orp : Σ[ o'' ∈ O ] Σ[ RR ∈ PType o'' ] (PP ⇝ RR)) → 
                 orp ≡ ⇝-f-⇝ F p →
                 ----------------------------------------------------
                 proj₁ (op ↓ₚₚ PP) ⊑ₒ proj₁ (op ↓ₚₚ proj₁ (proj₂ orp))

    ⇝-f-∈ₒ-aux (o'' , RR , r) q =
      ⇝-⊑ₒ (⇝-↓ₚ-cong r)

{- LEMMA 4.6 -}

⇝-f : {Γ : Ctx}
      {o o' : O} 
      {PP : PType o}
      {QQ : PType o'} →
      (F : Γ ⊢F⦂ PP) →
      (p : proj₂ (hole-ty-f F) ⇝ QQ) →
      ---------------------------------
      Γ ⊢F⦂ (proj₁ (proj₂ (⇝-f-⇝ F p)))

⇝-f [-] p =
  [-]
⇝-f (F ∥ₗ Q) p with ⇝-f F p
... | q =
  q ∥ₗ Q
⇝-f (Q ∥ᵣ F) p with ⇝-f F p
... | q =
  Q ∥ᵣ q
⇝-f (↑ op p V F) q with ⇝-f F q
... | r =
  ↑ op (⇝-f-∈ₒ F q op p) V r
⇝-f (↓ op V F) p with ⇝-f F p
... | q =
  ↓ op V q


⇝-f-tyₒ : {Γ : Ctx}
          {o o' : O}
          {PP : PType o}
          {QQ : PType o'} →
          (F : Γ ⊢F⦂ PP) →
          (p : proj₂ (hole-ty-f F) ⇝ QQ) →
          --------------------------------
          o' ≡ proj₁ (hole-ty-f (⇝-f F p))

⇝-f-tyₒ [-] p =
  refl
⇝-f-tyₒ (F ∥ₗ Q) p =
  ⇝-f-tyₒ F p
⇝-f-tyₒ (P ∥ᵣ F) p =
  ⇝-f-tyₒ F p
⇝-f-tyₒ (↑ op p V F) q =
  ⇝-f-tyₒ F q
⇝-f-tyₒ (↓ op V F) p =
  ⇝-f-tyₒ F p


⇝-f-ty : {Γ : Ctx}
         {o o' : O}
         {PP : PType o}
         {QQ : PType o'} →
         (F : Γ ⊢F⦂ PP) →
         (p : proj₂ (hole-ty-f F) ⇝ QQ) →
         --------------------------------------
         subst (λ o → PType o) (⇝-f-tyₒ F p) QQ
         ≡
         proj₂ (hole-ty-f (⇝-f F p))

⇝-f-ty [-] p =
  refl
⇝-f-ty (F ∥ₗ Q) p =
  ⇝-f-ty F p
⇝-f-ty (P ∥ᵣ F) p =
  ⇝-f-ty F p
⇝-f-ty (↑ op p V F) q =
  ⇝-f-ty F q
⇝-f-ty (↓ op V F) p =
  ⇝-f-ty F p


-- AUXILIARY TWO-LEVEL INDEXED SUBSTITUTION

subst-i : {X : Set} {x x' : X} → (Y : X → Set) → {y : Y x} {y' : Y x'} →
          (Z : (x : X) → Y x → Set) → (p : x ≡ x') → subst Y p y ≡ y' → Z x y → Z x' y'
subst-i Y Z refl refl z = z


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED PROCESSES
-- (ADDITIONALLY SERVES AS THE PRESERVATION THEOREM)

{- THEOREM 4.7 -}

infix 10 _[_]↝_

data _[_]↝_ {Γ : Ctx} : {o o' : O} {PP : PType o} {QQ : PType o'} → Γ ⊢P⦂ PP → PP ⇝ QQ → Γ ⊢P⦂ QQ → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run     : {X : VType}
            {o : O}
            {i : I}
            {M N : Γ ⊢M⦂ X ! (o , i)} → 
            M ↝ N →
            ---------------------------
            (run M) [ id ]↝ (run N)

  -- BROADCAST RULES

  ↑-∥ₗ    : {o o' : O}
            {PP : PType o}
            {QQ : PType o'}
            {op : Σₛ} → 
            (p : op ∈ₒ o) →
            (V : Γ ⊢V⦂ `` (payload op)) →
            (P : Γ ⊢P⦂ PP) →
            (Q : Γ ⊢P⦂ QQ) →
            ------------------------------------------
            ((↑ op p V P) ∥ Q)
            [ par ⇝-refl (⇝-↓ₚ {op = op}) ]↝
            ↑ op (∪ₒ-inl op p) V (P ∥ ↓ op V Q)

  ↑-∥ᵣ    : {o o' : O}
            {PP : PType o}
            {QQ : PType o'}
            {op : Σₛ} → 
            (p : op ∈ₒ o') →
            (V : Γ ⊢V⦂ `` (payload op)) →
            (P : Γ ⊢P⦂ PP) →
            (Q : Γ ⊢P⦂ QQ) →
            ------------------------------------------
            (P ∥ (↑ op p V Q))
            [ par (⇝-↓ₚ {op = op}) ⇝-refl ]↝
            ↑ op (∪ₒ-inr op p) V (↓ op V P ∥ Q)

  -- INTERRUPT PROPAGATION RULES

  ↓-run   : {X : VType}
            {o : O}
            {i : I}
            {op : Σₛ} → 
            (V : Γ ⊢V⦂ `` (payload op)) → 
            (M : Γ ⊢M⦂ X ! (o , i)) →
            -----------------------------
            ↓ op V (run M)
            [ id ]↝
            run (↓ op V M)

  ↓-∥     : {o o' : O}
            {PP : PType o}
            {QQ : PType o'}
            {op : Σₛ}
            (V : Γ ⊢V⦂ `` (payload op)) →
            (P : Γ ⊢P⦂ PP) →
            (Q : Γ ⊢P⦂ QQ) →
            -----------------------------
            ↓ op V (P ∥ Q)
            [ ⇝-refl ]↝
            ((↓ op V P) ∥ (↓ op V Q))

  ↓-↑     : {o : O}
            {PP : PType o}
            {op : Σₛ}
            {op' : Σₛ} →
            (p : op' ∈ₒ o) →
            (V : Γ ⊢V⦂ ``(payload op)) →
            (W : Γ ⊢V⦂ ``(payload op')) →
            (P : Γ ⊢P⦂ PP) →
            -----------------------------------
            ↓ op V (↑ op' p W P)
            [ ⇝-refl ]↝
            ↑ op' (↓ₚₚ-⊑ₒ PP op' p) W (↓ op V P)

  -- SIGNAL HOISTING RULE

  ↑       : {X : VType}
            {o : O}
            {i : I} → 
            {op : Σₛ} → 
            (p : op ∈ₒ o) →
            (V : Γ ⊢V⦂ `` (payload op)) →
            (M : Γ ⊢M⦂ X ! (o , i)) →
            -----------------------------
            run (↑ op p V M)
            [ id ]↝
            ↑ op p V (run M)

  -- EVALUATION CONTEXT RULE

  context : {o o' : O}
            {PP : PType o}
            {QQ : PType o'}
            (F : Γ ⊢F⦂ PP) →
            {P : Γ ⊢P⦂ proj₂ (hole-ty-f F)}
            {Q : Γ ⊢P⦂ QQ}
            {r : proj₂ (hole-ty-f F) ⇝ QQ} → 
            P [ r ]↝ Q →
            -----------------------------------------------------------------------------
            F [ P ]f
            [ proj₂ (proj₂ (⇝-f-⇝ F r)) ]↝
            (⇝-f F r) [ subst-i PType (λ o QQ → Γ ⊢P⦂ QQ) (⇝-f-tyₒ F r) (⇝-f-ty F r) Q ]f
