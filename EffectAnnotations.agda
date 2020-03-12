open import Data.Bool hiding (if_then_else_)
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Binary.PropositionalEquality hiding (Extensionality ; [_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module EffectAnnotations where

open import Axiom.Extensionality.Propositional


-- ASSUMING FUNCTION EXTENSIONALITY

postulate
  fun-ext : ∀ {a b} → Extensionality a b


-- SIGNAL AND INTERRUPT NAMES

postulate Σₛ : Set


-- SIGNAL AND INTERRUPT NAMES HAVE DECIDABLE EQUALITY

postulate decₛ : (op op' : Σₛ) → Dec (op ≡ op')

if_≡_then_else_ : {A : Set} → Σₛ → Σₛ → A → A → A
if op ≡ op' then x else y with decₛ op op'
... | yes p = x
... | no ¬p = y


ite-≡ : {A : Set}
        {op : Σₛ}
        {x y : A} →
        -----------------------------
        if op ≡ op then x else y ≡ x

ite-≡ {A} {op} with decₛ op op
ite-≡ {A} {op} | yes p =
  refl
ite-≡ {A} {op} | no ¬p =
  ⊥-elim (¬p refl)


ite-≢ : {A : Set}
        {op op' : Σₛ}
        {x y : A} →
        op ≢ op' →
        ------------------------------
        if op ≡ op' then x else y ≡ y

ite-≢ {A} {op} {op'} p with decₛ op op'
ite-≢ {A} {op} {op'} p | yes q =
  ⊥-elim (p q)
ite-≢ {A} {op} {op'} p | no ¬q =
  refl


-- EFFECT ANNOTATIONS FOR OUTGOING SIGNALS (O) AND INTERRUPT HANDLERS (I)

mutual
  data O : Set where
    omap : (Σₛ → Maybe ⊤) → O

  data I : Set where
    imap : (Σₛ → Maybe (O × I)) → I


-- EMPTY EFFECT ANNOTATIONS

∅ₒ : O
∅ₒ = omap (λ _ → nothing)

∅ᵢ : I
∅ᵢ = imap (λ _ → nothing)


-- UNION OF EFFECT ANNOTATIONS

∪ₒ-aux' : (o o' : Maybe ⊤) → Maybe ⊤
∪ₒ-aux' nothing o' = o'
∪ₒ-aux' (just tt) o' = just tt
  
∪ₒ-aux : (o o' : Σₛ → Maybe ⊤) → Σₛ → Maybe ⊤
∪ₒ-aux o o' op =
  ∪ₒ-aux' (o op) (o' op)

_∪ₒ_ : O → O → O
(omap o) ∪ₒ (omap o') =
  omap (∪ₒ-aux o o')


mutual
  ∪ᵢ-aux : (i i' : Σₛ → Maybe (O × I)) → Σₛ → Maybe (O × I)
  ∪ᵢ-aux i i' op =
    ∪ᵢ-aux' (i op) (i' op)

  ∪ᵢ-aux' : (oi oi' : Maybe (O × I)) → Maybe (O × I)
  ∪ᵢ-aux' nothing oi' =
    oi'
  ∪ᵢ-aux' (just oi'') nothing =
    just oi''
  ∪ᵢ-aux' (just (o'' , (imap i''))) (just (o''' , (imap i'''))) =
    just (o'' ∪ₒ o''' , imap (∪ᵢ-aux i'' i'''))

_∪ᵢ_ : I → I → I
(imap i) ∪ᵢ (imap i') =
  imap (∪ᵢ-aux i i')


-- SETTING THE VALUE OF EFFECT ANNOTATION AT A SPECIFIC INTERRUPT NAME

_[_↦_]ᵢ : I → Σₛ → Maybe (O × I) → I
(imap i) [ op ↦ v ]ᵢ =
  imap (λ op' → if op ≡ op' then v else i op')


-- ACTION OF INTERRUPTS ON EFFECT ANNOTATIONS

infix 40 _↓ₑ_

↓ₑ-auxₒ : Σₛ → Maybe (O × I) → O → O
↓ₑ-auxₒ op nothing o =
  o
↓ₑ-auxₒ op (just (o' , i')) o =
  o ∪ₒ o'

↓ₑ-auxᵢ : Σₛ → Maybe (O × I) → I → I
↓ₑ-auxᵢ op nothing i =
  i
↓ₑ-auxᵢ op (just (o' , i')) i =
  (i [ op ↦ nothing ]ᵢ) ∪ᵢ i'

_↓ₑ_ : Σₛ → O × I → O × I
op ↓ₑ (omap o , imap i) =
  (↓ₑ-auxₒ op (i op) (omap o) , ↓ₑ-auxᵢ op (i op) (imap i))


-- GENERALISED ACTION OF INTERRUPTS ON EFFECT ANNOTATIONS

_↓↓ₑ_ : List Σₛ → O × I → O × I
[] ↓↓ₑ (o , i) =
  (o , i)
(op ∷ ops) ↓↓ₑ (o , i) =
  op ↓ₑ (ops ↓↓ₑ (o , i))


↓↓ₑ-act : {o : O}
          {i : I} → 
          (ops ops' : List Σₛ) → 
          ------------------------------------------------------
          (ops ++ ops') ↓↓ₑ (o , i) ≡ ops ↓↓ₑ (ops' ↓↓ₑ (o , i))

↓↓ₑ-act [] ops' =
  refl
↓↓ₑ-act (op ∷ ops) ops' =
  cong (λ oi → op ↓ₑ oi) (↓↓ₑ-act ops ops')


-- CHECKING THE CONTENTS OF EFFECT ANNOTATIONS

_∈ₒ_ : Σₛ → O → Set
op ∈ₒ (omap o) =
  o op ≡ just tt


lkpᵢ : Σₛ → I → Maybe (O × I)
lkpᵢ op (imap i) = i op


-- SUBTYPING RELATIONS FOR EFFECT ANNOTATIONS

_⊑ₒ_ : O → O → Set
o ⊑ₒ o' = (op : Σₛ) → op ∈ₒ o → op ∈ₒ o'

data _⊑ᵢ_ (i i' : I) : Set where
  rel : ((op : Σₛ) → {o : O} → {i'' : I} → lkpᵢ op i ≡ just (o , i'') →
          Σ[ o' ∈ O ] Σ[ i''' ∈ I ] (lkpᵢ op i' ≡ just (o' , i''') × o ⊑ₒ o' × i'' ⊑ᵢ i''')) →
        i ⊑ᵢ i'
        

-- SUBTYPING RELATIONS ARE PREORDERS

⊑ₒ-refl : {o : O} →
          ---------
          o ⊑ₒ o
          
⊑ₒ-refl =
  λ op p → p


⊑ₒ-trans : {o o' o'' : O} →
           o ⊑ₒ o' →
           o' ⊑ₒ o'' →
           ----------------
           o ⊑ₒ o''
           
⊑ₒ-trans p q =
  λ op r → q op (p op r)


⊑ᵢ-refl : {i : I} →
          ---------
          i ⊑ᵢ i
         
⊑ᵢ-refl {imap i} =
  rel λ op {o'} → λ { {imap i'} → λ p → ⊑ᵢ-refl-aux (i op) p }

  where
    ⊑ᵢ-refl-aux : (oi : Maybe (O × I)) →
                  ----------------------------------------------------------------------------------
                  {o' : O} {i' : Σₛ → Maybe (O × I)} →
                  oi ≡ just (o' , imap i') →
                  Σ[ o'' ∈ O ] Σ[ i'' ∈ I ] (oi ≡ just (o'' , i'') × (o' ⊑ₒ o'') × (imap i' ⊑ᵢ i''))
                  
    ⊑ᵢ-refl-aux (just .(o' , imap i')) {o'} {i'} refl =
      o' , (imap i' , (refl , (⊑ₒ-refl , ⊑ᵢ-refl {imap i'})))


⊑ᵢ-trans : {i i' i'' : I} →
           i ⊑ᵢ i' →
           i' ⊑ᵢ i'' →
           -----------------
           i ⊑ᵢ i''

⊑ᵢ-trans {i} {i'} {i''} (rel p) (rel q) =
  rel λ op {o} {j} r → ⊑ᵢ-trans-aux o j op (p op r)

  where
    ⊑ᵢ-trans-aux' : (o : O) → (j : I) → (op : Σₛ) →
                    (o' : O) → (j' : I) → lkpᵢ op i' ≡ just (o' , j') → (o ⊑ₒ o') → (j ⊑ᵢ j') →
                    Σ[ o'' ∈ O ] Σ[ j'' ∈ I ] (lkpᵢ op i'' ≡ just (o'' , j'') × (o' ⊑ₒ o'') × (j' ⊑ᵢ j'')) →
                    Σ[ o'' ∈ O ] Σ[ j'' ∈ I ] (lkpᵢ op i'' ≡ just (o'' , j'') × (o ⊑ₒ o'') × (j ⊑ᵢ j''))
                    
    ⊑ᵢ-trans-aux' o j op o' j' r' s t (o'' , j'' , r'' , s' , t') =
      o'' , j'' , r'' , ⊑ₒ-trans s s' , ⊑ᵢ-trans t t'

    ⊑ᵢ-trans-aux : (o : O) → (j : I) → (op : Σₛ) →
                    Σ[ o' ∈ O ] Σ[ j' ∈ I ] (lkpᵢ op i' ≡ just (o' , j') × (o ⊑ₒ o') × (j ⊑ᵢ j')) →
                    Σ[ o'' ∈ O ] Σ[ j'' ∈ I ] (lkpᵢ op i'' ≡ just (o'' , j'') × (o ⊑ₒ o'') × (j ⊑ᵢ j''))
                    
    ⊑ᵢ-trans-aux o j op (o' , j' , r' , s , t) =
      ⊑ᵢ-trans-aux' o j op o' j' r' s t (q op r')


-- LEFT UNIT FOR UNIONS OF EFFECT ANNOTATIONS

∪ₒ-lunit : (o : O) →
           -----------
           ∅ₒ ∪ₒ o ≡ o

∪ₒ-lunit (omap o) =
  cong omap (fun-ext ∪ₒ-lunit-aux)

  where
    ∪ₒ-lunit-aux : (op : Σₛ) →
                   ----------------------------------
                   ∪ₒ-aux (λ _ → nothing) o op ≡ o op
                   
    ∪ₒ-lunit-aux op with o op 
    ... | nothing =
      refl
    ... | just _ =
      refl


∪ᵢ-lunit : (i : I) →
           -----------
           ∅ᵢ ∪ᵢ i ≡ i

∪ᵢ-lunit (imap i) = cong imap (fun-ext ∪ᵢ-lunit-aux)

  where
    ∪ᵢ-lunit-aux : (op : Σₛ) →
                   ----------------------------------
                   ∪ᵢ-aux (λ _ → nothing) i op ≡ i op

    ∪ᵢ-lunit-aux op with i op
    ... | nothing =
      refl
    ... | just _ =
      refl


-- LEFT AND RIGHT INCLUSIONS INTO UNIONS OF EFFECT ANNOTATIONS

∪ₒ-inl : {o o' : O} →
         -------------
         o ⊑ₒ (o ∪ₒ o')

∪ₒ-inl {omap o} {omap o'} op with o op | o' op
... | nothing | nothing = λ p → p
... | nothing | just tt = λ _ → refl
... | just tt | nothing = λ p → p
... | just tt | just tt = λ p → p


∪ₒ-inr : {o o' : O} →
         -------------
         o' ⊑ₒ (o ∪ₒ o')

∪ₒ-inr {omap o} {omap o'} op with o op | o' op
... | nothing | nothing = λ p → p
... | nothing | just tt = λ p → p
... | just tt | nothing = λ _ → refl
... | just tt | just tt = λ p → p


∪ᵢ-inl : {i i' : I} →
        -------------
        i ⊑ᵢ (i ∪ᵢ i')

∪ᵢ-inl {imap i} {imap i'} =
  rel (λ op → ∪ᵢ-inl-aux (i op) (i' op))

  where
    ∪ᵢ-inl-aux : (oi oi' : Maybe (O × I)) →
                 {o : O} {i'' : I} →
                 oi ≡ just (o , i'') →
                 Σ[ o' ∈ O ] Σ[ i''' ∈ I ] (∪ᵢ-aux' oi oi' ≡ just (o' , i''') × (o ⊑ₒ o') × (i'' ⊑ᵢ i'''))
                 
    ∪ᵢ-inl-aux (just .(o , i'')) nothing {o} {i''} refl =
      o , i'' , refl , ⊑ₒ-refl , ⊑ᵢ-refl
    ∪ᵢ-inl-aux (just .(o , imap i'')) (just (o' , imap i''')) {o} {imap i''} refl =
      o ∪ₒ o' , imap (∪ᵢ-aux i'' i''') , refl , ∪ₒ-inl , ∪ᵢ-inl


∪ᵢ-inr : {i i' : I} →
        -------------
        i' ⊑ᵢ (i ∪ᵢ i')

∪ᵢ-inr {imap i} {imap i'} =
  rel (λ op → ∪ᵢ-inr-aux (i op) (i' op))

  where
    ∪ᵢ-inr-aux : (oi oi' : Maybe (O × I)) →
                 {o : O} {i'' : I} →
                 oi' ≡ just (o , i'') →
                 Σ[ o' ∈ O ] Σ[ i''' ∈ I ] (∪ᵢ-aux' oi oi' ≡ just (o' , i''') × (o ⊑ₒ o') × (i'' ⊑ᵢ i'''))
                 
    ∪ᵢ-inr-aux nothing (just .(o , i'')) {o} {i''} refl =
      o , i'' , refl , ⊑ₒ-refl , ⊑ᵢ-refl
    ∪ᵢ-inr-aux (just (o' , imap i''')) (just .(o , imap i'')) {o} {imap i''} refl =
      o' ∪ₒ o , imap (∪ᵢ-aux i''' i'') , refl , ∪ₒ-inr , ∪ᵢ-inr


-- COPAIRING FOR UNIONS OF EFFECT ANNOTATIONS

∪ₒ-copair : {o o' o'' : O} →
            o ⊑ₒ o'' →
            o' ⊑ₒ o'' →
            ----------------
            (o ∪ₒ o') ⊑ₒ o''

∪ₒ-copair {omap o} {omap o'} {omap o''} p q op =
  ∪ₒ-copair-aux (p op) (q op)

  where
    ∪ₒ-copair-aux : (p : op ∈ₒ (omap o) → op ∈ₒ (omap o'')) →
                    (q : op ∈ₒ (omap o') → op ∈ₒ (omap o'')) →
                    ---------------------------------------------
                    op ∈ₒ (omap (∪ₒ-aux o o')) → op ∈ₒ (omap o'')

    ∪ₒ-copair-aux p q with o op | o' op
    ... | nothing | nothing = q
    ... | nothing | just tt = q
    ... | just tt | nothing = p
    ... | just tt | just tt = p


inj-just : {X : Set} {x x' : X} → just x ≡ just x' → x ≡ x'
inj-just refl = refl

inj-pair₁ : {X Y : Set} {x x' : X} {y y' : Y} → (x , y) ≡ (x' , y') → x ≡ x'
inj-pair₁ refl = refl

inj-pair₂ : {X Y : Set} {x x' : X} {y y' : Y} → (x , y) ≡ (x' , y') → y ≡ y'
inj-pair₂ refl = refl


∪ᵢ-copair : {i i' i'' : I} →
            i ⊑ᵢ i'' →
            i' ⊑ᵢ i'' →
            ----------------
            (i ∪ᵢ i') ⊑ᵢ i''

∪ᵢ-copair {imap i} {imap i'} {imap i''} (rel p) (rel q) =
  rel (λ op {o'''} {i'''} r → ∪ᵢ-copair-aux op o''' i''' (i op) (i' op) (i'' op) refl refl refl r)

  where
    ∪ᵢ-copair-aux : (op : Σₛ) →
                    (o''' : O) →
                    (i''' : I)
                    (oi oi' oi'' : Maybe (O × I)) →
                    (oi ≡ i op) →
                    (oi' ≡ i' op) →
                    (oi'' ≡ i'' op) →
                    (r : ∪ᵢ-aux' oi oi' ≡ just (o''' , i''')) → 
                    Σ[ o' ∈ O ] Σ[ i'''' ∈ I ] (oi'' ≡ just (o' , i'''') × (o''' ⊑ₒ o') × (i''' ⊑ᵢ i''''))
                      
    ∪ᵢ-copair-aux op o''' i''' nothing (just oi') nothing r s t u with trans t (proj₁ (proj₂ (proj₂ (q op (trans (sym s) u)))))
    ... | ()
    ∪ᵢ-copair-aux op o''' i''' nothing (just oi') (just oi'') r s t u =
      proj₁ (q op (trans (sym s) u)) ,
      proj₁ (proj₂ (q op (trans (sym s) u))) ,
      trans t (proj₁ (proj₂ (proj₂ (q op (trans (sym s) u))))) ,
      proj₁ (proj₂ (proj₂ (proj₂ (q op (trans (sym s) u))))) ,
      proj₂ (proj₂ (proj₂ (proj₂ (q op (trans (sym s) u)))))
    ∪ᵢ-copair-aux op o''' i''' (just oi) nothing oi'' r s t u =
      proj₁ (p op (trans (sym r) u)) ,
      proj₁ (proj₂ (p op (trans (sym r) u))) ,
      trans t (proj₁ (proj₂ (proj₂ (p op (trans (sym r) u))))) ,
      proj₁ (proj₂ (proj₂ (proj₂ (p op (trans (sym r) u))))) ,
      proj₂ (proj₂ (proj₂ (proj₂ (p op (trans (sym r) u)))))
    ∪ᵢ-copair-aux op o''' i'''
                  (just (omap o'''' , imap i''''))
                  (just (omap o''''' , imap i'''''))
                  nothing r s t u
                  with trans t (proj₁ (proj₂ (proj₂ (p op (sym r)))))
    ... | ()
    ∪ᵢ-copair-aux op o''' i'''
                  (just (omap o'''' , imap i''''))
                  (just (omap o''''' , imap i'''''))
                  (just (omap o'''''' , imap i''''''))
                  r s t u
                  with inj-pair₁ (inj-just u) | inj-pair₂ (inj-just u)
    ... | v | w =
      omap o'''''' ,
      imap i'''''' ,
      refl ,
      subst (λ o → o ⊑ₒ omap o'''''')
            v
            (∪ₒ-copair (subst (λ o → omap o'''' ⊑ₒ o)
                              (inj-pair₁ (inj-just (sym (trans t (proj₁ (proj₂ (proj₂ (p op (sym r)))))))))
                              (proj₁ (proj₂ (proj₂ (proj₂ (p op (sym r)))))))
                       (subst (λ o → omap o''''' ⊑ₒ o)
                              (inj-pair₁ (inj-just (sym (trans t (proj₁ (proj₂ (proj₂ (q op (sym s)))))))))
                              (proj₁ (proj₂ (proj₂ (proj₂ (q op (sym s)))))))) ,
      subst (λ i → i ⊑ᵢ imap i'''''')
             w
             (∪ᵢ-copair (subst (λ i → imap i'''' ⊑ᵢ i)
                               (inj-pair₂ (inj-just (sym (trans t (proj₁ (proj₂ (proj₂ (p op (sym r)))))))))
                               (proj₂ (proj₂ (proj₂ (proj₂ (p op (sym r)))))))
                        ((subst (λ i → imap i''''' ⊑ᵢ i)
                               (inj-pair₂ (inj-just (sym (trans t (proj₁ (proj₂ (proj₂ (q op (sym s)))))))))
                               (proj₂ (proj₂ (proj₂ (proj₂ (q op (sym s)))))))))


-- FUNCTORIALITY OF UNIONS OF EFFECT ANNOTATIONS

∪ₒ-fun : {o o' o'' o''' : O} →
         o ⊑ₒ o'' → 
         o' ⊑ₒ o''' →
         --------------------------
         (o ∪ₒ o') ⊑ₒ (o'' ∪ₒ o''')

∪ₒ-fun p q =
  ∪ₒ-copair (⊑ₒ-trans p ∪ₒ-inl) (⊑ₒ-trans q ∪ₒ-inr)


∪ᵢ-fun : {i i' i'' i''' : I} →
         i ⊑ᵢ i'' → 
         i' ⊑ᵢ i''' →
         --------------------------
         (i ∪ᵢ i') ⊑ᵢ (i'' ∪ᵢ i''')

∪ᵢ-fun p q =
  ∪ᵢ-copair (⊑ᵢ-trans p ∪ᵢ-inl) (⊑ᵢ-trans q ∪ᵢ-inr)


-- UNIONS OF INTERRUPT ANNOTATIONS ARE GIVEN BY POINTWISE UNIONS

∪ᵢ-∪ₒ : {op : Σₛ}
        {o'' o''' o'''' : O}
        {i i' i'' i''' i'''' : I} → 
        lkpᵢ op (i ∪ᵢ i') ≡ just (o'' , i'') →
        lkpᵢ op i ≡ just (o''' , i''') →
        lkpᵢ op i' ≡ just (o'''' , i'''') →
        ---------------------------------------
        o'' ≡ o''' ∪ₒ o''''

∪ᵢ-∪ₒ {op} {o''} {o'''} {o''''} {imap i} {imap i'} p q r with i op | i' op
∪ᵢ-∪ₒ {op} {.(o''' ∪ₒ o'''')} {o'''} {o''''} {imap i} {imap i'} {_} {imap i'''} {imap i''''}
  refl refl refl | just .(o''' , imap i''') | just .(o'''' , imap i'''') =
    refl

∪ᵢ-∪ᵢ : {op : Σₛ}
        {o'' o''' o'''' : O}
        {i i' i'' i''' i'''' : I} → 
        lkpᵢ op (i ∪ᵢ i') ≡ just (o'' , i'') →
        lkpᵢ op i ≡ just (o''' , i''') →
        lkpᵢ op i' ≡ just (o'''' , i'''') →
        ---------------------------------------
        i'' ≡ i''' ∪ᵢ i''''

∪ᵢ-∪ᵢ {op} {o''} {o'''} {o''''} {imap i} {imap i'} p q r with i op | i' op
∪ᵢ-∪ᵢ {op} {.(o''' ∪ₒ o'''')} {o'''} {o''''} {imap i} {imap i'} {_} {imap i'''} {imap i''''}
  refl refl refl | just .(o''' , imap i''') | just .(o'''' , imap i'''') =
    refl


-- INCLUSION INTO ACTED UPON EFFECT ANNOTATION

{- LEMMA 3.1 (1) -}

↓ₑ-⊑ₒ : {o : O}
        {i : I}
        {op : Σₛ} →
        --------------------------
        o ⊑ₒ proj₁ (op ↓ₑ (o , i))
                           
↓ₑ-⊑ₒ {omap o} {imap i} {op} op' p with i (op)
... | nothing = p
... | just (o' , i') = ∪ₒ-inl op' p


{- LEMMA 3.1 (2) - the O part -}

↓ₑ-⊑ₒ-o' : {o o' : O}
           {i i' : I}
           {op : Σₛ} → 
           lkpᵢ op i ≡ just (o' , i') → 
           ---------------------------
           o' ⊑ₒ proj₁ (op ↓ₑ (o , i))

↓ₑ-⊑ₒ-o' {omap o} {omap o'} {imap i} {imap i'} {op} p with i (op)
↓ₑ-⊑ₒ-o' {omap o} {omap o'} {imap i} {imap i'} {op} refl | just .(omap o' , imap i') =
  ↓ₑ-⊑ₒ-o'-aux

  where
    ↓ₑ-⊑ₒ-o'-aux : (op' : Σₛ) → o' op' ≡ just tt → ∪ₒ-aux o o' op' ≡ just tt
    ↓ₑ-⊑ₒ-o'-aux op' p with o op'
    ↓ₑ-⊑ₒ-o'-aux op' p | nothing = p
    ↓ₑ-⊑ₒ-o'-aux op' p | just tt = refl


{- LEMMA 3.1 (2) - the I part -}

↓ₑ-⊑ₒ-i' : {o o' : O}
           {i i' : I}
           {op : Σₛ} → 
           lkpᵢ op i ≡ just (o' , i') → 
           ---------------------------
           i' ⊑ᵢ proj₂ (op ↓ₑ (o , i))

↓ₑ-⊑ₒ-i' {omap o} {omap o'} {imap i} {imap i'} {op} p with i (op)
↓ₑ-⊑ₒ-i' {omap o} {omap o'} {imap i} {imap i'} {op} refl | just .(omap o' , imap i') =
  rel ↓ₑ-⊑ₒ-i'-aux

  where
    ↓ₑ-⊑ₒ-i'-aux : (op' : Σₛ) {o'' : O} {i'' : I} →
      i' op' ≡ just (o'' , i'') →
      Σ[ o''' ∈ O ] Σ[ i''' ∈ I ] (∪ᵢ-aux (λ op' → if op ≡ op' then nothing else i op') i' op' ≡ just (o''' , i''') ×
                                  (o'' ⊑ₒ o''') × (i'' ⊑ᵢ i'''))
    ↓ₑ-⊑ₒ-i'-aux op' {o''} {i''} p with decₛ op op'
    ↓ₑ-⊑ₒ-i'-aux op' {o''} {i''} p | yes refl with i' (op)
    ↓ₑ-⊑ₒ-i'-aux op' {o''} {i''} refl | yes refl | just .(o'' , i'') =
      o'' , (i'' , refl , (⊑ₒ-refl , ⊑ᵢ-refl))
    ↓ₑ-⊑ₒ-i'-aux op' {o''} {i''} p | no ¬q with i (op') | i' (op') 
    ↓ₑ-⊑ₒ-i'-aux op' {o''} {i''} refl | no ¬q | nothing | just .(o'' , i'') =
      o'' , (i'' , refl , (⊑ₒ-refl , ⊑ᵢ-refl))
    ↓ₑ-⊑ₒ-i'-aux op' {o''} {imap i''} refl | no ¬q | just (o''' , (imap i''')) | just .(o'' , (imap i'')) =
      (o''' ∪ₒ o'') , (imap (∪ᵢ-aux i''' i'') , (refl , (∪ₒ-inr , ∪ᵢ-inr)))


-- EFFECT ANNOTATION OF AN INTERRUPT THAT WAS NOT ACTED WITH

{- LEMMA 3.1 (3) -}

lkpᵢ-↓ₑ-neq : {o o' : O}
              {i i' : I} {op op' : Σₛ} →
              ¬ op ≡ op' →
              lkpᵢ op' i ≡ just (o' , i') →
              -------------------------------------------------------------------------------------------------------
              Σ[ o'' ∈ O ] Σ[ i'' ∈ I ] (lkpᵢ op' (proj₂ (op ↓ₑ (o , i))) ≡ just (o'' , i'') × o' ⊑ₒ o'' × i' ⊑ᵢ i'')
             
lkpᵢ-↓ₑ-neq {omap o} {o'} {imap i} {imap i'} {op} {op'} p q with i (op)
... | nothing =
  o' , imap i' , q , ⊑ₒ-refl , ⊑ᵢ-refl
lkpᵢ-↓ₑ-neq {omap o} {o'} {imap i} {imap i'} {op} {op'} p q | just (o'' , imap i'') with decₛ op op'
... | yes r with p r
... | ()
lkpᵢ-↓ₑ-neq {omap o} {o'} {imap i} {imap i'} {op} {op'} p q | just (o'' , imap i'') | no ¬r with i (op') | i'' (op')
lkpᵢ-↓ₑ-neq {omap o} {.o'''} {imap i} {imap i'} {op} {op'} p refl |
  just (o'' , imap i'') | no ¬r | just (o''' , .(imap i')) | nothing =
    o''' , imap i' , refl , ⊑ₒ-refl , ⊑ᵢ-refl
... | just (o''' , imap i''') | just (o'''' , imap i'''') with q
lkpᵢ-↓ₑ-neq {omap o} {.o'''} {imap i} {imap .i'''} {op} {op'} p q |
  just (o'' , imap i'') | no ¬r | just (o''' , imap i''') | just (o'''' , imap i'''') | refl =
    (o''' ∪ₒ o'''') , (imap i''') ∪ᵢ (imap i'''') , refl , ∪ₒ-inl , ∪ᵢ-inl


-- NEXT DEFINED EFFECT ANNOTATION UNDER SUBTYPING EFFECT ANNOTATIONS

lkpᵢ-nextₒ : {o'' : O} {i i' i'' : I} {op : Σₛ} →
            i ⊑ᵢ i' → lkpᵢ op i ≡ just (o'' , i'') → O
            
lkpᵢ-nextₒ {o''} {i} {i'} {i''} {op} (rel p) q =
  proj₁ (p op q)


lkpᵢ-nextᵢ : {o'' : O} {i i' i'' : I} {op : Σₛ} →
            i ⊑ᵢ i' → lkpᵢ op i ≡ just (o'' , i'') → I

lkpᵢ-nextᵢ {o''} {i} {i'} {i''} {op} (rel p) q =
  proj₁ (proj₂ (p op q))


lkpᵢ-next-eq : {o'' : O} {i i' i'' : I} {op : Σₛ} →
              (p : i ⊑ᵢ i') →
              (q : lkpᵢ op i ≡ just (o'' , i'')) →
              ------------------------------------------------
              lkpᵢ op i' ≡ just (lkpᵢ-nextₒ p q , lkpᵢ-nextᵢ p q)

lkpᵢ-next-eq {o''} {i} {i'} {i''} {op} (rel p) q =
  proj₁ (proj₂ (proj₂ (p op q)))


lkpᵢ-next-⊑ₒ : {o'' : O} {i i' i'' : I} {op : Σₛ} →
              (p : i ⊑ᵢ i') →
              (q : lkpᵢ op i ≡ just (o'' , i'')) →
              -----------------------------------
              o'' ⊑ₒ lkpᵢ-nextₒ p q

lkpᵢ-next-⊑ₒ {o''} {i} {i'} {i''} {op} (rel p) q =
  proj₁ (proj₂ (proj₂ (proj₂ (p op q))))


lkpᵢ-next-⊑ᵢ : {o'' : O} {i i' i'' : I} {op : Σₛ} →
              (p : i ⊑ᵢ i') →
              (q : lkpᵢ op i ≡ just (o'' , i'')) →
              -----------------------------------
              i'' ⊑ᵢ lkpᵢ-nextᵢ p q

lkpᵢ-next-⊑ᵢ {o''} {i} {i'} {i''} {op} (rel p) q =
  proj₂ (proj₂ (proj₂ (proj₂ (p op q))))


-- ACTION OF INTERRUPTS ON EFFECT ANNOTATIONS IS MONOTONIC

mutual 
  ↓ₑ-monotonicₒ : {o o' : O}
                  {i i' : I}
                  {op : Σₛ} →
                  o ⊑ₒ o' →
                  i ⊑ᵢ i' →
                  ------------------------------------------------
                  proj₁ (op ↓ₑ (o , i)) ⊑ₒ proj₁ (op ↓ₑ (o' , i'))

  ↓ₑ-monotonicₒ {omap o} {omap o'} {imap i} {imap i'} {op} p (rel q) =
    ↓ₑ-monotonicₒ-aux (i op) (i' op) refl refl

    where
      ↓ₑ-monotonicₒ-aux : (oi oi' : Maybe (O × I)) →
                          i op ≡ oi →
                          i' op ≡ oi' →
                          ----------------------------
                          ↓ₑ-auxₒ op oi (omap o)
                          ⊑ₒ
                          ↓ₑ-auxₒ op oi' (omap o')

      ↓ₑ-monotonicₒ-aux nothing nothing r s =
        p
      ↓ₑ-monotonicₒ-aux nothing (just (omap o''' , imap i''')) r s =
        ⊑ₒ-trans p ∪ₒ-inl
      ↓ₑ-monotonicₒ-aux (just (omap o'' , imap i'')) nothing r s with trans (sym s) (proj₁ (proj₂ (proj₂ (q op r))))
      ... | ()
      ↓ₑ-monotonicₒ-aux (just (omap o'' , imap i'')) (just (omap o''' , imap i''')) r s with trans (sym s) (proj₁ (proj₂ (proj₂ (q op r))))
      ... | t =
        ∪ₒ-fun p (⊑ₒ-trans (proj₁ (proj₂ (proj₂ (proj₂ (q op r)))))
                           (subst (λ o → o ⊑ₒ omap o''') (inj-pair₁ (inj-just t)) ⊑ₒ-refl))


  ↓ₑ-monotonicᵢ : {o o' : O}
                {i i' : I}
                {op : Σₛ} →
                o ⊑ₒ o' →
                i ⊑ᵢ i' →
                ------------------------------------------------
                proj₂ (op ↓ₑ (o , i)) ⊑ᵢ proj₂ (op ↓ₑ (o' , i'))

  ↓ₑ-monotonicᵢ {omap o} {omap o'} {imap i} {imap i'} {op} p (rel q) =
    ↓ₑ-monotonicᵢ-aux (i op) (i' op) refl refl

    where
      ↓ₑ-monotonicᵢ-aux : (oi oi' : Maybe (O × I)) →
                          oi ≡ i op →
                          oi' ≡ i' op →
                          -----------------------------------------
                          ↓ₑ-auxᵢ op oi (imap i)
                          ⊑ᵢ
                          ↓ₑ-auxᵢ op oi' (imap i')

      ↓ₑ-monotonicᵢ-aux nothing nothing r s =
        rel q
      ↓ₑ-monotonicᵢ-aux nothing (just (omap o''' , imap i''')) r s =
        ⊑ᵢ-trans (rel (λ op' {o''''} {i''''} t → ↓ₑ-monotonicᵢ-aux' op' o'''' i'''' t))
                 (∪ᵢ-inl {(imap i') [ op ↦ nothing ]ᵢ} {imap i'''})

        where
          ↓ₑ-monotonicᵢ-aux' : (op' : Σₛ) → 
                               (o'''' : O) → 
                               (i'''' : I) →
                               i op' ≡ just (o'''' , i'''') → 
                               --------------------------------------------------------------------
                               Σ[ o''''' ∈ O ] Σ[ i''''' ∈ I ]
                                 ((if op ≡ op' then nothing else i' op') ≡ just (o''''' , i''''') ×
                                  (o'''' ⊑ₒ o''''') × (i'''' ⊑ᵢ i'''''))

          ↓ₑ-monotonicᵢ-aux' op' o'''' i'''' t with decₛ op op'
          ↓ₑ-monotonicᵢ-aux' op' o'''' i'''' t | yes refl with trans r t
          ... | ()
          ↓ₑ-monotonicᵢ-aux' op' o'''' i'''' t | no ¬u =
            lkpᵢ-nextₒ (rel q) t ,
            lkpᵢ-nextᵢ (rel q) t ,
            lkpᵢ-next-eq (rel q) t ,
            lkpᵢ-next-⊑ₒ (rel q) t ,
            lkpᵢ-next-⊑ᵢ (rel q) t

      ↓ₑ-monotonicᵢ-aux (just (omap o'' , imap i'')) nothing r s with trans s (proj₁ (proj₂ (proj₂ (q op (sym r)))))
      ... | ()
        
      ↓ₑ-monotonicᵢ-aux (just (omap o'' , imap i'')) (just (omap o''' , imap i''')) r s =
        ∪ᵢ-fun {_}
               {imap i''}
               {_}
               {imap i'''}
               (rel λ op' {o''''} {i''''} t → ↓ₑ-monotonicᵢ-aux' op' o'''' i'''' t)
               (subst (λ i → imap i'' ⊑ᵢ i)
                      (sym (inj-pair₂ (inj-just (trans s (proj₁ (proj₂ (proj₂ (q op (sym r)))))))))
                      (proj₂ (proj₂ (proj₂ (proj₂ (q op (sym r)))))))


        where
          ↓ₑ-monotonicᵢ-aux' : (op' : Σₛ) →
                               (o'''' : O) →
                               (i'''' : I) →
                               lkpᵢ op' (imap i [ op ↦ nothing ]ᵢ)  ≡ just (o'''' , i'''') →
                               --------------------------
                               Σ[ o''''' ∈ O ] Σ[ i''''' ∈ I ]
                                 (lkpᵢ op' (imap i' [ op ↦ nothing ]ᵢ)
                                  ≡ just (o''''' , i''''') ×
                                  (o'''' ⊑ₒ o''''') × (i'''' ⊑ᵢ i'''''))

          ↓ₑ-monotonicᵢ-aux' op' o'''' i'''' t with decₛ op op'
          ↓ₑ-monotonicᵢ-aux' op' o'''' i'''' t | no ¬u =
            lkpᵢ-nextₒ (rel q) t ,
            lkpᵢ-nextᵢ (rel q) t ,
            lkpᵢ-next-eq (rel q) t ,
            lkpᵢ-next-⊑ₒ (rel q) t ,
            lkpᵢ-next-⊑ᵢ (rel q) t


-- GENERALISED ACTION OF INTERRUPTS ON EFFECT ANNOTATIONS IS MONOTONIC

mutual 
  ↓↓ₑ-monotonicₒ : {o o' : O}
                   {i i' : I} → 
                   (ops : List Σₛ) →
                   o ⊑ₒ o' →
                   i ⊑ᵢ i' →
                   ----------------------------------------------------
                   proj₁ (ops ↓↓ₑ (o , i)) ⊑ₒ proj₁ (ops ↓↓ₑ (o' , i'))

  ↓↓ₑ-monotonicₒ {omap o} {omap o'} {imap i} {imap i'} [] p q =
    p
  ↓↓ₑ-monotonicₒ (op ∷ ops) p q =
    ↓ₑ-monotonicₒ (↓↓ₑ-monotonicₒ ops p q) (↓↓ₑ-monotonicᵢ ops p q)


  ↓↓ₑ-monotonicᵢ : {o o' : O}
                   {i i' : I} → 
                   (ops : List Σₛ) →
                   o ⊑ₒ o' →
                   i ⊑ᵢ i' →
                   ----------------------------------------------------
                   proj₂ (ops ↓↓ₑ (o , i)) ⊑ᵢ proj₂ (ops ↓↓ₑ (o' , i'))

  ↓↓ₑ-monotonicᵢ [] p q = q
  ↓↓ₑ-monotonicᵢ (op ∷ ops) p q =
    ↓ₑ-monotonicᵢ (↓↓ₑ-monotonicₒ ops p q) (↓↓ₑ-monotonicᵢ ops p q)


-- INCLUSION INTO GENERALLY ACTED UPON EFFECT ANNOTATION

↓↓ₑ-⊑ₒ : {o : O}
         {i : I} → 
         (ops : List Σₛ) →
         --------------------------
         o ⊑ₒ proj₁ (ops ↓↓ₑ (o , i))

↓↓ₑ-⊑ₒ [] =
  ⊑ₒ-refl
↓↓ₑ-⊑ₒ (op ∷ ops) =
  ⊑ₒ-trans (↓↓ₑ-⊑ₒ ops) (↓ₑ-⊑ₒ {op = op})


-- A PATH OF INTERRUPT NAMES THAT REVEALS THE GIVEN SIGNAL IN AN EFFECT ANNOTATION

data _`at_`in_,_ (op : Σₛ) : List Σₛ → O → I → Set where

  stop : {o : O}
         {i : I} →
         op ∈ₒ o →
         -------------------
         op `at [] `in o , i
         
  next : {o o' : O}
         {i i' : I}
         {op' : Σₛ}
         {ops : List Σₛ} →
         lkpᵢ op' i ≡ just (o' , i') →
         op `at ops `in o' , i' →
         -----------------------------
         op `at (op' ∷ ops) `in o , i


-- ACTING ON AN ANNOTATION WITH EMPTY SIGNALS PART JUST REVEALS THE INNER LAYER IF THE INTERRUPTS MATCH

↓ₑ-∅-↦-≡ : {op : Σₛ}
           {o : O}
           {i : I} →
           -----------------------------
           op ↓ₑ (∅ₒ , imap (λ op' → if op' ≡ op then just (o , i) else nothing))
           ≡
           (o , i)

↓ₑ-∅-↦-≡ {op} {o} {i} with decₛ op op
↓ₑ-∅-↦-≡ {op} {omap o} {i} | yes refl =
  cong₂ (λ x y → x , y)
        (∪ₒ-lunit (omap o))
        (trans (cong (λ i' → i' ∪ᵢ i) ↓ₑ-∅-↦-≡-aux) (∪ᵢ-lunit i))

  where
    ↓ₑ-∅-↦-≡-aux : imap (λ op' → if op ≡ op' then nothing else (if op' ≡ op then just (omap o , i) else nothing))
                   ≡
                   ∅ᵢ

    ↓ₑ-∅-↦-≡-aux = cong imap (fun-ext ↓ₑ-∅-↦-≡-aux-aux)

      where
        ↓ₑ-∅-↦-≡-aux-aux : (op' : Σₛ) →
                           ---------------------------------------------------------------------------------
                           (if op ≡ op' then nothing else (if op' ≡ op then just (omap o , i) else nothing))
                           ≡
                           nothing

        ↓ₑ-∅-↦-≡-aux-aux op' with decₛ op op'
        ... | yes refl =
          refl
        ... | no ¬p =
          ite-≢ (λ q → ¬p (sym q))


↓ₑ-∅-↦-≡ {op} {o} {i} | no ¬p =
  ⊥-elim (¬p refl)


-- ACTING ON AN ANNOTATION WITH EMPTY SIGNALS IS IDEMPOTENT IF THE INTERRUPTS DO NOT MATCH

↓ₑ-∅-↦-≢ : {op op' : Σₛ}
           {o : O}
           {i : I} →
           op ≢ op' → 
           -----------------------------
           op' ↓ₑ (∅ₒ , imap (λ op'' → if op'' ≡ op then just (o , i) else nothing))
           ≡
           (∅ₒ , imap (λ op'' → if op'' ≡ op then just (o , i) else nothing))

↓ₑ-∅-↦-≢ {op} {op'} p with decₛ op' op
↓ₑ-∅-↦-≢ {op} {.op} p | yes refl =
  ⊥-elim (p refl)
↓ₑ-∅-↦-≢ {op} {op'} p | no ¬q =
  refl


-- A MINIMAL EFFECT ANNOTATION SUCH THAT A GIVEN PATH OF INTERRUPTS REVEALS THE GIVEN SIGNAL NAME

mutual 
  ⦃⦃_↦_⦄⦄ₒ : List Σₛ → Σₛ → O
  ⦃⦃ [] ↦ op ⦄⦄ₒ =
    omap (λ op' → if op ≡ op' then just tt else nothing)
  ⦃⦃ op' ∷ ops ↦ op ⦄⦄ₒ =
    ∅ₒ


  ⦃⦃_↦_⦄⦄ᵢ : List Σₛ → Σₛ → I
  ⦃⦃ [] ↦ op ⦄⦄ᵢ =
    ∅ᵢ
  ⦃⦃ op' ∷ ops ↦ op ⦄⦄ᵢ =
    imap (λ op'' → if op'' ≡ op' then just (⦃⦃ ops ↦ op ⦄⦄ₒ , ⦃⦃ ops ↦ op ⦄⦄ᵢ) else nothing)


-- IF THERE IS A PATH TO A SIGNAL IN AN EFFECT ANNOTATION, THE MINIMAL EFFECT ANNOTATION IS INCLUDED IN IT

mutual 
  `at-minₒ : {op : Σₛ}
             {ops : List Σₛ}
             {o : O}
             {i : I} →
             op `at ops `in o , i →
             ----------------------
             ⦃⦃ ops ↦ op ⦄⦄ₒ ⊑ₒ o

  `at-minₒ {op} {_} {omap o} (stop p) op' with decₛ op op'
  `at-minₒ {.op'} {.[]} {omap o} (stop p) op' | yes refl =
    λ _ → p
  `at-minₒ {op} {.[]} {omap o} (stop p) op'' | no ¬q =
    λ ()
  `at-minₒ (next p q) op'' =
    λ ()


  `at-minᵢ : {op : Σₛ}
             {ops : List Σₛ}
             {o : O}
             {i : I} →
             op `at ops `in o , i →
             ----------------------
             ⦃⦃ ops ↦ op ⦄⦄ᵢ ⊑ᵢ i

  `at-minᵢ (stop p) =
    rel (λ op'' → λ ())
  `at-minᵢ {op} (next {o} {o'} {i} {i'} {op'} {ops} p q) =
    rel (λ op'' {o''} {i''} r → `at-minᵢ-aux r)

    where
      `at-minᵢ-aux : {op'' : Σₛ}
                     {o'' : O}
                     {i'' : I} →
                     lkpᵢ op'' ⦃⦃ op' ∷ ops ↦ op ⦄⦄ᵢ ≡ just (o'' , i'') →
                     ---------------------------------------------------
                     Σ[ o''' ∈ O ]
                     Σ[ i''' ∈ I ]
                     (lkpᵢ op'' i ≡ just (o''' , i''') ×
                      (o'' ⊑ₒ o''') ×
                      (i'' ⊑ᵢ i'''))

      `at-minᵢ-aux {op''} p with decₛ op'' op'
      `at-minᵢ-aux {op'} refl | yes refl =
        o' , i' , p , `at-minₒ q , `at-minᵢ q


-- SUBPATHS OF (INTERRUPT) NAMES

data _⊆_ : List Σₛ → List Σₛ → Set where

  [] : {ops' : List Σₛ} →
         ----------------
         [] ⊆ ops'
        
  ∷-≡  : {op : Σₛ}
         {ops ops' : List Σₛ} →
         ops ⊆ ops' →
         ------------------------
         (op ∷ ops) ⊆ (op ∷ ops')

  ∷-≢  : {op op' : Σₛ}
         {ops ops' : List Σₛ} →
         op ≢ op' →
         (op ∷ ops) ⊆ ops' →
         -------------------------
         (op ∷ ops) ⊆ (op' ∷ ops')

mutual 
  ∷-≢-swap : {op op' : Σₛ}
             {ops ops' : List Σₛ} →
             op ≢ op' →
             (op ∷ ops) ⊆ (op' ∷ op ∷ ops') →
             --------------------------------
             (op ∷ ops) ⊆ (op ∷ op' ∷ ops')

  ∷-≢-swap {op} {.op} {ops} {ops'} p (∷-≡ q) =
    ∷-≡ q
  ∷-≢-swap {op} {op'} {ops} {ops'} p (∷-≢ q (∷-≡ r)) =
    ∷-≡ (∷-∷ r)
  ∷-≢-swap {op} {op'} {ops} {ops'} p (∷-≢ q (∷-≢ r s)) =
    ⊥-elim (r refl)


  ∷-∷ : {op' : Σₛ}
        {ops : List Σₛ} →
        {ops' : List Σₛ} → 
        ops ⊆ ops' →
        -------------------
        ops ⊆ (op' ∷ ops')

  ∷-∷ [] = []
  ∷-∷ {op'} (∷-≡ {op} p) with decₛ op op'
  ∷-∷ {.op} (∷-≡ {op} p) | yes refl =
    ∷-≡ (∷-∷ p)
  ∷-∷ {op'} (∷-≡ {op} p) | no ¬q =
    ∷-≢ ¬q (∷-≡ p)
  ∷-∷ {op'} (∷-≢ {op} {op''} p q) with decₛ op op'
  ∷-∷ {.op} (∷-≢ {op} {op''} p q) | yes refl = ∷-≢-swap p (∷-≢ p (∷-∷ q))
  ∷-∷ {op'} (∷-≢ {op} {op''} p q) | no ¬r = ∷-≢ ¬r (∷-≢ p q)


-- IF A SUBPATH OF INTERRUPTS REVEALS A SIGNAL, THEN ACTING WITH THE WHOLE PATH ALSO REVEALS IT
           
⊆-↓↓ : {op : Σₛ}
       {ops ops' : List Σₛ} →
       ops ⊆ ops' →
       ---------------------------------------------------------------
       op ∈ₒ proj₁ (reverse ops' ↓↓ₑ (⦃⦃ ops ↦ op ⦄⦄ₒ , ⦃⦃ ops ↦ op ⦄⦄ᵢ))

⊆-↓↓ {op} {ops} {ops'} [] =
  (↓↓ₑ-⊑ₒ (reverse ops')) op ⊆-↓↓-aux

  where
    ⊆-↓↓-aux : (if op ≡ op then just tt else nothing) ≡ just tt
    ⊆-↓↓-aux with decₛ op op 
    ⊆-↓↓-aux | yes refl =
      refl
    ⊆-↓↓-aux | no ¬p =
      ⊥-elim (¬p refl)

⊆-↓↓ {op} (∷-≡ {op'} {ops} {ops'} p) =
  subst (λ ops'' → op ∈ₒ proj₁ (ops'' ↓↓ₑ (⦃⦃ (op' ∷ ops) ↦ op ⦄⦄ₒ , ⦃⦃ (op' ∷ ops) ↦ op ⦄⦄ᵢ)))
        (sym (unfold-reverse op' ops'))
        (subst (λ oi → op ∈ₒ proj₁ oi)
               (sym (↓↓ₑ-act (reverse ops') [ op' ]))
               (subst (λ oi → op ∈ₒ proj₁ (reverse ops' ↓↓ₑ oi))
                      (sym ↓ₑ-∅-↦-≡)
                      (⊆-↓↓ p)))

⊆-↓↓ {op} (∷-≢ {op'} {op''} {ops} {ops'} p q) =
  subst (λ ops'' → op ∈ₒ proj₁ (ops'' ↓↓ₑ (⦃⦃ (op' ∷ ops) ↦ op ⦄⦄ₒ , ⦃⦃ (op' ∷ ops) ↦ op ⦄⦄ᵢ)))
        (sym (unfold-reverse op'' ops'))
        (subst (λ oi → op ∈ₒ proj₁ oi)
               (sym (↓↓ₑ-act (reverse ops') [ op'' ]))
               (subst (λ oi → op ∈ₒ proj₁ (reverse ops' ↓↓ₑ oi))
                      (sym (↓ₑ-∅-↦-≢ p))
                      (⊆-↓↓ q)))


-- IF A PATH REVEALS A SIGNAL IN A UNION OF EFFECT ANNOTATIONS, THE PATH REVEALS THE SIGNAL IN ONE OF THE SUMMANDS

`at-⊎ : {op : Σₛ}
        {ops : List Σₛ}
        {o o' : O}
        {i i' : I} →
        op `at ops `in (o ∪ₒ o') , (i ∪ᵢ i') →
        -------------------------------------------------
        (op `at ops `in o , i) ⊎ (op `at ops `in o' , i')

`at-⊎ {op} {ops} {omap o} {omap o'} {i} {i'} (stop p) =
  `at-⊎-aux p (o op) (o' op) refl refl

  where
    `at-⊎-aux : (∪ₒ-aux o o' op ≡ just tt) →
                (t t' : Maybe ⊤) →
                o op ≡ t →
                o' op ≡ t' →
                -----------------------------------------------------------
                (op `at ops `in omap o , i) ⊎ (op `at ops `in omap o' , i')

    `at-⊎-aux p nothing nothing q r with o op | o' op
    `at-⊎-aux () nothing nothing q r | nothing | nothing
    `at-⊎-aux p nothing nothing q () | nothing | just tt
    `at-⊎-aux p nothing (just tt) q r =
      inj₂ (stop r)
    `at-⊎-aux p (just tt) t' q r =
      inj₁ (stop q)

`at-⊎ {op} {_} {o} {o'} {imap i} {imap i'} (next {o''} {o'''} {i''} {i'''} {op'} {ops} p q) =
  `at-⊎-aux p q (i op') (i' op') refl refl

  where
    `at-⊎-aux : ∪ᵢ-aux i i' op' ≡ just (o''' , i''') →
                op `at ops `in o''' , i''' →
                (oi oi' : Maybe (O × I)) →
                i op' ≡ oi →
                i' op' ≡ oi' →
                ---------------------------------------------------------------------------
                (op `at (op' ∷ ops) `in o , imap i) ⊎ (op `at (op' ∷ ops) `in o' , imap i')

    `at-⊎-aux p q nothing nothing r s with i op' | i' op'
    `at-⊎-aux () q nothing nothing r s | nothing | nothing
    `at-⊎-aux p q nothing nothing r () | nothing | just _
    `at-⊎-aux p q nothing (just (o'''' , i'''')) r s =
      inj₂ (next (trans (sym (`at-⊎-aux-aux r s)) p) q)

      where
        `at-⊎-aux-aux : i op' ≡ nothing → 
                        i' op' ≡ just (o'''' , i'''') →
                        -------------------------------
                        ∪ᵢ-aux i i' op' ≡ i' op'

        `at-⊎-aux-aux r s with i op' | i' op' 
        `at-⊎-aux-aux r s | nothing | just _ =
          refl

    `at-⊎-aux p q (just (o'''' , i'''')) nothing r s =
      inj₁ (next (trans (sym (`at-⊎-aux-aux r s)) p) q)

      where
        `at-⊎-aux-aux : i op' ≡ just (o'''' , i'''') → 
                        i' op' ≡ nothing →
                        -------------------------------
                        ∪ᵢ-aux i i' op' ≡ i op'

        `at-⊎-aux-aux r s with i op' | i' op' 
        `at-⊎-aux-aux r s | just _ | nothing =
          refl

    `at-⊎-aux p q (just (o'''' , i'''')) (just (o''''' , i''''')) r s
      with ∪ᵢ-∪ₒ {i = imap i} {i' = imap i'} p r s | ∪ᵢ-∪ᵢ {i = imap i} {i' = imap i'} p r s
    ... | refl | refl with `at-⊎ q
    ... | inj₁ t =
      inj₁ (next r t)
    ... | inj₂ t =
      inj₂ (next s t)


-- IF ACTING WITH A PATH REVEALS A SIGNAL, THEN THERE IS A SUBPATH TO THAT SIGNAL

↓↓-⊆-rw : (o : O)
          (i : I)
          (op : Σₛ)
          (ops : List Σₛ) →
          ----------------------------------------------------------------
          reverse (op ∷ ops) ↓↓ₑ (o , i) ≡ reverse ops ↓↓ₑ (op ↓ₑ (o , i))

↓↓-⊆-rw o i op ops =
  trans (cong (λ ops' → ops' ↓↓ₑ (o , i)) (unfold-reverse op ops))
        (↓↓ₑ-act (reverse ops) [ op ])

↓↓-⊆ : {op : Σₛ} → 
       (ops : List Σₛ) → 
       {o : O}
       {i : I} →
       op ∈ₒ proj₁ (reverse ops ↓↓ₑ (o , i)) → 
       ----------------------------------------------------------
       Σ[ ops' ∈ List Σₛ ] (ops' ⊆ ops × (op `at ops' `in o , i))

↓↓-⊆ [] p =
  [] , [] , stop p
↓↓-⊆ {op} (op' ∷ ops) {omap o} {imap i} p rewrite ↓↓-⊆-rw (omap o) (imap i) op' ops =
  ↓↓-⊆-aux (i op') refl

  where
    ↓↓-⊆-aux : (oi : Maybe (O × I)) →
               i op' ≡ oi →
               ----------------------------------------------------------------------------
               Σ[ ops' ∈ List Σₛ ] (ops' ⊆ (op' ∷ ops) × (op `at ops' `in omap o , imap i))

    ↓↓-⊆-aux nothing q with ↓↓-⊆ ops p
    ... | ops' , r , s rewrite q =
      ops' , ∷-∷ r , s
    ↓↓-⊆-aux (just (omap o' , imap i')) q with ↓↓-⊆ ops p
    ... | ops' , r , s rewrite q with `at-⊎ {o = omap o} {o' = omap o'} {i' = imap i'} s 
    ... | inj₁ t =
      ↓↓-⊆-aux-aux ops' r t

      where
        ↓↓-⊆-aux-aux : (ops' : List Σₛ) →
                       ops' ⊆ ops →
                       (op `at ops' `in omap o , ((imap i) [ op' ↦ nothing ]ᵢ)) → 
                       -------------------------------------------------------------------------------
                       Σ[ ops'' ∈ List Σₛ ] (ops'' ⊆ (op' ∷ ops) × (op `at ops'' `in omap o , imap i))

        ↓↓-⊆-aux-aux [] r (stop t) =
          [] , [] , stop t
        ↓↓-⊆-aux-aux (op'' ∷ ops'') r (next t u) with decₛ op' op''
        ... | no ¬v =
          op'' ∷ ops'' , ∷-≢ (λ w → ¬v (sym w)) r , next t u

    ... | inj₂ t =
      op' ∷ ops' , ∷-≡ r , next q t


-- ENVELOPING THE EFFECT ANNOTATION REDUCTION WITH MLTIPLE INTERRUPT ACTIONS

{- LEMMA 4.6 -}

↓↓ₑ-⊑ₒ-act : {o : O}
             {i : I} → 
             (ops : List Σₛ) →
             (op : Σₛ) →
             ----------------------------------------------------------
             proj₁ (ops ↓↓ₑ (o , i)) ⊑ₒ proj₁ (ops ↓↓ₑ (op ↓ₑ (o , i)))

↓↓ₑ-⊑ₒ-act {o} {i} ops op op' p rewrite sym (reverse-involutive ops) with ↓↓-⊆ (reverse ops) p
... | ops' , q , r with ⊆-↓↓ {op'} (∷-∷ {op} q)
... | s with ↓↓ₑ-monotonicₒ (reverse (op ∷ reverse ops)) (`at-minₒ r) (`at-minᵢ r) op' s
... | t rewrite ↓↓-⊆-rw o i op (reverse ops) | reverse-involutive ops = t
