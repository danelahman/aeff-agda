open import Data.List renaming (_∷_ to _∷∷_ ; [_] to ⟦_⟧)
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

-- WELL-TYPED SIGNAL HOISTING CONTEXTS

data _⊢H[_]⦂_ (Γ : Ctx) : (Δ : BCtx) → CType → Set where

  [-]              : {C : CType} →
                     -------------
                     Γ ⊢H[ [] ]⦂ C

  promise_∣_↦_`in_ : {Δ : BCtx}
                     {X Y : VType}
                     {o o' : O}
                     {i i' : I} → 
                     (op : Σₛ) →
                     lkpᵢ op i ≡ just (o' , i') →
                     Γ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i') →
                     Γ ∷ ⟨ X ⟩ ⊢H[ Δ ]⦂ Y ! (o , i) →
                     ------------------------------------------
                     Γ ⊢H[ X ∷∷ Δ ]⦂ Y ! (o , i)


-- FINDING THE TYPE OF THE HOLE OF A WELL-TYPED SIGNAL HOISTING CONTEXT

hole-ty-hₒ : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
             Γ ⊢H[ Δ ]⦂ X ! (o , i) → O
hole-ty-hₒ {_} {_} {_} {o} [-] =
  o
hole-ty-hₒ (promise op ∣ p ↦ M `in H) =
  hole-ty-hₒ H


hole-ty-hᵢ : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
             Γ ⊢H[ Δ ]⦂ X ! (o , i) → I
hole-ty-hᵢ {_} {_} {_} {_} {o} [-] =
  o
hole-ty-hᵢ (promise op ∣ p ↦ M `in H) =
  hole-ty-hᵢ H


{- LEMMA 4.7 (1) - the O part -}

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


{- LEMMA 4.7 (1) - the I part -}

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


-- FILLING A WELL-TYPED SIGNAL HOISTING CONTEXT WITH A COMPUTATION

infix 30 _[_]h

_[_]h : {Γ : Ctx} {Δ : BCtx} {X : VType} {o : O} {i : I} →
        (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) → Γ ⋈ Δ ⊢M⦂ (X ! (hole-ty-hₒ H , hole-ty-hᵢ H)) →
        Γ ⊢M⦂ X ! (o , i)
[-] [ M ]h =
  M
(promise op ∣ p ↦ N `in E) [ M ]h =
  promise op ∣ p ↦ N `in (E [ M ]h)
  

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
        (o'' , i'') ≡ ((ops ++ ⟦ op ⟧) ↓↓ₑ (o , i)) → 
        ---------------------------------------------
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

{- LEMMA 4.5 (1) -}

⇝-refl : {o : O} {PP : PType o} → PP ⇝ PP
⇝-refl {o} {X ‼ o , i} =
  id
⇝-refl {.(_ ∪ₒ _)} {PP ∥ QQ} =
  par ⇝-refl ⇝-refl


-- ACTION OF INTERRUPTS ON GENERAL PROCESS TYPES IS A REDUCTION

{- LEMMA 4.5 (2) -}

⇝-↓ : {o : O}
      {PP : PType o}
      {op : Σₛ} →
      --------------
      PP ⇝ op ↓ₚ PP

⇝-↓ {.o} {X ‼ o , i} {op} =
  act [] op refl refl
⇝-↓ {.(_ ∪ₒ _)} {PP ∥ QQ} {op} =
  par ⇝-↓ ⇝-↓


-- ACTION OF INTERRUPTS PRESERVES PROCESS TYPE REDUCTION

{- LEMMA 4.5 (3) -}

⇝-↓ₚ : {o o' : O}
       {PP : PType o}
       {QQ : PType o'}
       {op : Σₛ} →
       PP ⇝ QQ → 
       --------------------
       op ↓ₚ PP ⇝ op ↓ₚ QQ

⇝-↓ₚ id =
  id
⇝-↓ₚ {_} {_} {_} {_} {op} (act {_} {o} {o'} {o''} {i} {i'} {i''} ops op' p q) =
  act {o = o} {i = i} (op ∷∷ ops) op' (cong (λ oi → op ↓ₑ oi) p) (cong (λ oi → op ↓ₑ oi) q) 
⇝-↓ₚ (par p q) =
  par (⇝-↓ₚ p) (⇝-↓ₚ q)


-- PROCESS TYPE REDUCTION INCREASES SIGNAL INDEX

{- LEMMA 4.5 (4) -}

inj-proj₁ : {X Y : Set} {xy xy' : X × Y} → xy ≡ xy' → proj₁ xy ≡ proj₁ xy'
inj-proj₁ refl = refl

⇝-↓ₚ-⊑ₒ : {o o' : O}
          {PP : PType o}
          {QQ : PType o'} →
          PP ⇝ QQ →
          ------------------
          o ⊑ₒ o'

⇝-↓ₚ-⊑ₒ id =
  ⊑ₒ-refl
⇝-↓ₚ-⊑ₒ (act {_} {o} {o'} {o''} {i} ops op p q) with inj-proj₁ p | inj-proj₁ q
... | r | s = 
  subst (λ o → o ⊑ₒ o'')
        (sym r)
        (subst (λ o'' → proj₁ (ops ↓↓ₑ (o , i)) ⊑ₒ o'')
               (sym s)
               (subst (λ v → proj₁ (ops ↓↓ₑ (o , i)) ⊑ₒ proj₁ v)
                      (sym (↓↓ₑ-act ops ⟦ op ⟧))
                      (↓↓ₑ-⊑ₒ-act ops op)))
⇝-↓ₚ-⊑ₒ (par p q) =
  ∪ₒ-fun (⇝-↓ₚ-⊑ₒ p) (⇝-↓ₚ-⊑ₒ q)


-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-var : {Γ : Ctx} → (Δ : BCtx) → {A : BType} → `` A ∈ Γ ⋈ Δ → `` A ∈ Γ
strengthen-var [] x = x
strengthen-var (y ∷∷ Δ) x with strengthen-var Δ x
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

{- LEMMA 4.7 (2) -}

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
  proj₁ (op ↓ₚₚ RR) , (op ↓ₚ RR) , ⇝-↓ₚ q


⇝-f-∈ₒ : {Γ : Ctx}
         {o o' : O}
         {PP : PType o}
         {QQ : PType o'}
         (F : Γ ⊢F⦂ PP) →
         (p : proj₂ (hole-ty-f F) ⇝ QQ) →
         --------------------------------
         o ⊑ₒ proj₁ (⇝-f-⇝ F p)

⇝-f-∈ₒ [-] p =
  ⇝-↓ₚ-⊑ₒ p
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
      ⇝-↓ₚ-⊑ₒ (⇝-↓ₚ r)


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

{- THEOREM 4.8 -}

infix 10 _[_]↝_

data _[_]↝_ {Γ : Ctx} : {o o' : O} {PP : PType o} {QQ : PType o'} → Γ ⊢P⦂ PP → PP ⇝ QQ → Γ ⊢P⦂ QQ → Set where

  -- RUNNING INDIVIDUAL COMPUTATIONS

  run   : {X : VType}
          {o : O}
          {i : I}
          {M N : Γ ⊢M⦂ X ! (o , i)} → 
          M ↝ N →
          ---------------------------
          (run M) [ id ]↝ (run N)

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
           [ par ⇝-refl (⇝-↓ {op = op}) ]↝
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
           [ par (⇝-↓ {op = op}) ⇝-refl ]↝
           ↑ op (∪ₒ-inr op p) V (↓ op V P ∥ Q)

  -- INTERRUPT RULES

  ↓-run : {X : VType}
          {o : O}
          {i : I}
          {op : Σₛ} → 
          (V : Γ ⊢V⦂ `` (payload op)) → 
          (M : Γ ⊢M⦂ X ! (o , i)) →
          -----------------------------
          ↓ op V (run M)
          [ id ]↝
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
          [ ⇝-refl ]↝
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
          [ ⇝-refl ]↝
          ↑ op' (↓ₚ-⊑ₒ PP op' p) W (↓ op V P)

  -- HOISTING RULE

  ↑     : {Δ : BCtx}
          {X : VType}
          {o o' : O}
          {i i' : I} → 
          (H : Γ ⊢H[ Δ ]⦂ X ! (o , i)) → 
          {op : Σₛ} → 
          (p : op ∈ₒ hole-ty-hₒ H) →
          (V : Γ ⋈ Δ ⊢V⦂ `` (payload op)) →
          (M : Γ ⋈ Δ ⊢M⦂ X ! (hole-ty-hₒ H , hole-ty-hᵢ H)) →
          ----------------------------------------------------------------------
          run (H [ ↑ op p V M ]h)
          [ id ]↝
          ↑ op (hole-ty-h-⊑ₒ H op p) (strengthen-val {Δ = Δ} V) (run (H [ M ]h))

  -- CONTEXT RULE

  context : {o o' : O}
            {PP : PType o}
            {QQ : PType o'}
            {F : Γ ⊢F⦂ PP}
            {P : Γ ⊢P⦂ proj₂ (hole-ty-f F)}
            {Q : Γ ⊢P⦂ QQ}
            {p : proj₂ (hole-ty-f F) ⇝ QQ} → 
            P [ p ]↝ Q →
            --------------------------------
            F [ P ]f
            [ proj₂ (proj₂ (⇝-f-⇝ F p)) ]↝
            (⇝-f F p) [ subst-i PType (λ o QQ → Γ ⊢P⦂ QQ) (⇝-f-tyₒ F p) (⇝-f-ty F p) Q ]f
