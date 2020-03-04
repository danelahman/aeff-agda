open import Data.Bool hiding (if_then_else_)
open import Data.Empty
open import Data.List renaming (_∷_ to _∷∷_ ; [_] to ⟦_⟧)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary
open import Relation.Nullary.Negation

module EffectAnnotations where

open import Axiom.Extensionality.Propositional

postulate
  fun-ext : ∀ {a b} → Extensionality a b                      -- assuming function extensionality


-- SIGNAL AND INTERRUPT NAMES

postulate Σₛ : Set                                            -- set of signal and interrupt names

postulate decₛ : (op op' : Σₛ) → Dec (op ≡ op')               -- signal and interrupt names have decidable equality

if_≡_then_else_ : {A : Set} → Σₛ → Σₛ → A → A → A
if op ≡ op' then x else y =
  if' (decₛ op op') then x else y

  where
    if'_then_else_ : {A : Set} {op op' : Σₛ} → Dec (op ≡ op') → A → A → A
    if' yes p then x else y = x
    if' no ¬p then x else y = y

-- EFFECT ANNOTATIONS

mutual
  data O : Set where                                         -- set of effect annotations of outgoing signals
    omap : (Σₛ → Maybe ⊤) → O

  data I : Set where                                         -- set of effect annotations of incoming interrupts
    imap : (Σₛ → Maybe (O × I)) → I


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


-- IDEMPOTENCE OF EFFECT ANNOTATIONS

∪ₒ-idem : (o : O) → o ∪ₒ o ≡ o
∪ₒ-idem (omap o) =
  cong omap (fun-ext (λ op → ∪ₒ-idem-aux (o op) (o op)))

  where
    ∪ₒ-idem-aux : (o o' : Maybe ⊤) →
                  ------------------
                  ∪ₒ-aux' o o ≡ o
                  
    ∪ₒ-idem-aux nothing nothing = refl
    ∪ₒ-idem-aux nothing (just tt) = refl
    ∪ₒ-idem-aux (just tt) nothing = refl
    ∪ₒ-idem-aux (just tt) (just tt) = refl


-- SETTING THE VALUE OF EFFECT ANNOTATION AT AN INTERRUPT

_[_↦_]ᵢ : I → Σₛ → Maybe (O × I) → I
(imap i) [ op ↦ v ]ᵢ =
  imap λ op' → if op ≡ op' then v else i op'


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
(op ∷∷ ops) ↓↓ₑ (o , i) =
  op ↓ₑ (ops ↓↓ₑ (o , i))


↓↓ₑ-act : {o : O}
          {i : I} → 
          (ops ops' : List Σₛ) → 
          ------------------------------------------------------
          (ops ++ ops') ↓↓ₑ (o , i) ≡ ops ↓↓ₑ (ops' ↓↓ₑ (o , i))

↓↓ₑ-act [] ops' =
  refl
↓↓ₑ-act (op ∷∷ ops) ops' =
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
          
⊑ₒ-refl = λ op p → p


⊑ₒ-trans : {o o' o'' : O} →
           o ⊑ₒ o' →
           o' ⊑ₒ o'' →
           ----------------
           o ⊑ₒ o''
           
⊑ₒ-trans p q = λ op r → q op (p op r)


⊑ᵢ-refl : {i : I} →
         ----------
         i ⊑ᵢ i
         
⊑ᵢ-refl {imap i} =
  rel λ op {o'} → λ { {imap i'} → λ p → ⊑ᵢ-refl-aux (i op) p }

  where
    ⊑ᵢ-refl-aux : (oi : Maybe (O × I)) →
                  -----------------------------------------------------------------------------------
                  {o' : O} {i' : Σₛ → Maybe (O × I)} →
                  oi ≡ just (o' , imap i') →
                  Σ[ o'' ∈ O ] Σ[ i'' ∈ I ] (oi ≡ just (o'' , i'') × (o' ⊑ₒ o'') × (imap i' ⊑ᵢ i''))
    ⊑ᵢ-refl-aux (just .(o' , imap i')) {o'} {i'} refl =
      o' , (imap i' , (refl , (⊑ₒ-refl , ⊑ᵢ-refl {imap i'})))


⊑ᵢ-trans : {i i' i'' : I} →
          i ⊑ᵢ i' →
          i' ⊑ᵢ i'' →
          ----------------
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

lkpᵢ-↓ₑ-neq : {o o' : O} {i i' : I} {op op' : Σₛ} → ¬ op ≡ op' → lkpᵢ op' i ≡ just (o' , i') →
             Σ[ o'' ∈ O ] Σ[ i'' ∈ I ] (lkpᵢ op' (proj₂ (op ↓ₑ (o , i))) ≡ just (o'' , i'') × o' ⊑ₒ o'' × i' ⊑ᵢ i'')
lkpᵢ-↓ₑ-neq {omap o} {o'} {imap i} {imap i'} {op} {op'} p q with i (op)
... | nothing =
  o' , imap i' , q , ⊑ₒ-refl , ⊑ᵢ-refl
lkpᵢ-↓ₑ-neq {omap o} {o'} {imap i} {imap i'} {op} {op'} p q | just (o'' , imap i'') with decₛ op op'
... | yes r with p r
... | ()
lkpᵢ-↓ₑ-neq {omap o} {o'} {imap i} {imap i'} {op} {op'} p q | just (o'' , imap i'') | no ¬r with i (op') | i'' (op')
lkpᵢ-↓ₑ-neq {omap o} {.o'''} {imap i} {imap i'} {op} {op'} p refl | just (o'' , imap i'')
                                                                 | no ¬r
                                                                 | just (o''' , .(imap i'))
                                                                 | nothing =
  o''' , imap i' , refl , ⊑ₒ-refl , ⊑ᵢ-refl
... | just (o''' , imap i''') | just (o'''' , imap i'''') with q
lkpᵢ-↓ₑ-neq {omap o} {.o'''} {imap i} {imap .i'''} {op} {op'} p q | just (o'' , imap i'')
                                                                 | no ¬r
                                                                 | just (o''' , imap i''')
                                                                 | just (o'''' , imap i'''') | refl =
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


-- ETA LAW FOR SETTING THE VALUE OF EFFECT ANNOTATION AT AN INTERRUPT

↓ₑ-↦-eta : (i : I) → 
           (op : Σₛ) →
           (oi : Maybe (O × I)) → 
           lkpᵢ op i ≡ oi →
           ------------------------
           i ≡ (i [ op ↦ oi ]ᵢ)

↓ₑ-↦-eta (imap i) op oi p =
  cong (λ i → imap i) (fun-ext (λ op' → ↓ₑ-↦-eta-aux op'))

  where
    ↓ₑ-↦-eta-aux : (op' : Σₛ) →
                   ----------------------------------------
                   i op' ≡ (if op ≡ op' then oi else i op')

    ↓ₑ-↦-eta-aux op' with decₛ op op'
    ... | yes refl = p
    ... | no ¬q = refl


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
  ↓↓ₑ-monotonicₒ (op ∷∷ ops) p q =
    ↓ₑ-monotonicₒ (↓↓ₑ-monotonicₒ ops p q) (↓↓ₑ-monotonicᵢ ops p q)


  ↓↓ₑ-monotonicᵢ : {o o' : O}
                   {i i' : I} → 
                   (ops : List Σₛ) →
                   o ⊑ₒ o' →
                   i ⊑ᵢ i' →
                   ----------------------------------------------------
                   proj₂ (ops ↓↓ₑ (o , i)) ⊑ᵢ proj₂ (ops ↓↓ₑ (o' , i'))

  ↓↓ₑ-monotonicᵢ [] p q = q
  ↓↓ₑ-monotonicᵢ (op ∷∷ ops) p q =
    ↓ₑ-monotonicᵢ (↓↓ₑ-monotonicₒ ops p q) (↓↓ₑ-monotonicᵢ ops p q)


-- INCLUSION INTO GENERALLY ACTED UPON EFFECT ANNOTATION

↓↓ₑ-⊑ₒ : {o : O}
         {i : I} → 
         (ops : List Σₛ) →
         --------------------------
         o ⊑ₒ proj₁ (ops ↓↓ₑ (o , i))

↓↓ₑ-⊑ₒ [] =
  ⊑ₒ-refl
↓↓ₑ-⊑ₒ (op ∷∷ ops) =
  ⊑ₒ-trans (↓↓ₑ-⊑ₒ ops) (↓ₑ-⊑ₒ {op = op})


-- ENVELOPING THE EFFECT ANNOTATION REDUCTION WITH A SINGLE INTERRUPT ACTION

↓↓ₑ-⊑ₒ-act₁-≡ : {o o' : O}
                {i i' : I} →
                (op : Σₛ) →
                lkpᵢ op i ≡ just (o' , i') → 
                ----------------------------------------------------------------------------------
                proj₁ (op ↓ₑ (o , i)) ⊑ₒ proj₁ (op ↓ₑ ((o ∪ₒ o') , ((i [ op ↦ nothing ]ᵢ) ∪ᵢ i')))

↓↓ₑ-⊑ₒ-act₁-≡ {omap o} {omap o'} {imap i} {imap i'} op p with i op
↓↓ₑ-⊑ₒ-act₁-≡ {omap o} {omap o'} {imap i} {imap i'} op refl | just (.(omap o') , .(imap i')) with decₛ op op
↓↓ₑ-⊑ₒ-act₁-≡ {omap o} {omap o'} {imap i} {imap i'} op refl | just (.(omap o') , .(imap i')) | yes refl with i' op
↓↓ₑ-⊑ₒ-act₁-≡ {omap o} {omap o'} {imap i} {imap i'} op refl | just (.(omap o') , .(imap i')) | yes refl | nothing =
  ⊑ₒ-refl
↓↓ₑ-⊑ₒ-act₁-≡ {omap o} {omap o'} {imap i} {imap i'} op refl | just (.(omap o') , .(imap i')) | yes refl | just _ =
  ∪ₒ-inl
↓↓ₑ-⊑ₒ-act₁-≡ {omap o} {omap o'} {imap i} {imap i'} op refl | just (.(omap o') , .(imap i')) | no ¬p =
  ⊥-elim (¬p refl)


↓↓ₑ-⊑ₒ-act₁-≢ : {o o' : O}
                {i i' : I} →
                (op op' : Σₛ) →
                op ≢ op' → 
                lkpᵢ op' i ≡ just (o' , i') → 
                -----------------------------------------------------------------------------------
                proj₁ (op ↓ₑ (o , i)) ⊑ₒ proj₁ (op ↓ₑ ((o ∪ₒ o') , ((i [ op' ↦ nothing ]ᵢ) ∪ᵢ i')))

↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} {imap i} {imap i'} op op' p q with i op
↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} {imap i} {imap i'} op op' p q | nothing with decₛ op' op
↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} {imap i} {imap i'} op op' p q | nothing | yes r =
  ⊥-elim (p (sym r))
↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} {imap i} {imap i'} op op' p q | nothing | no ¬r with i' op
↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} {imap i} {imap i'} op op' p q | nothing | no ¬r | nothing =
  ∪ₒ-inl
↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} {imap i} {imap i'} op op' p q | nothing | no ¬r | just _ =
  ⊑ₒ-trans ∪ₒ-inl ∪ₒ-inl 
↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} {imap i} {imap i'} op op' p q | just (o'' , i'') with decₛ op' op
↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} {imap i} {imap i'} op op' p q | just (o'' , i'') | yes r =
  ⊥-elim (p (sym r))
↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} {imap i} {imap i'} op op' p q | just (o'' , i'') | no ¬r with i' op
↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} {imap i} {imap i'} op op' p q | just (o'' , i'') | no ¬r | nothing =
  ∪ₒ-copair (⊑ₒ-trans ∪ₒ-inl ∪ₒ-inl) ∪ₒ-inr
↓↓ₑ-⊑ₒ-act₁-≢ {omap o} {omap o'} op op' p q | just (omap o'' , imap i'') | no ¬r | just (omap o''' , imap i''') =
  ∪ₒ-copair {omap o} {omap o''} {((omap o) ∪ₒ (omap o')) ∪ₒ ((omap o'') ∪ₒ (omap o'''))}
            (⊑ₒ-trans ∪ₒ-inl ∪ₒ-inl)
            (⊑ₒ-trans (∪ₒ-inl {omap o''} {omap o'''} ) (∪ₒ-inr {(omap o) ∪ₒ (omap o')} {(omap o'') ∪ₒ (omap o''')}))


↓↓ₑ-⊑ₒ-act₁ : {o : O}
              {i : I}
              (op op' : Σₛ) →
              -------------------------------------------------------
              proj₁ (op ↓ₑ (o , i)) ⊑ₒ proj₁ (op ↓ₑ (op' ↓ₑ (o , i)))

↓↓ₑ-⊑ₒ-act₁ {omap o} {imap i} op op' =
  ↓↓ₑ-⊑ₒ-act₁-aux {o} {i} op op' (i op') refl

  where
    ↓↓ₑ-⊑ₒ-act₁-aux : {o : Σₛ → Maybe ⊤}
                      {i : Σₛ → Maybe (O × I)}
                      (op op' : Σₛ) → 
                      (oi : Maybe (O × I)) → 
                      i op' ≡ oi →
                      -----------------------------------------------------------------
                      proj₁ (op ↓ₑ (omap o , imap i))
                      ⊑ₒ
                      proj₁ (op ↓ₑ (↓ₑ-auxₒ op' oi (omap o) , ↓ₑ-auxᵢ op' oi (imap i)))

    ↓↓ₑ-⊑ₒ-act₁-aux {o} {i} op op' nothing p =
      ⊑ₒ-refl
    ↓↓ₑ-⊑ₒ-act₁-aux {o} {i} op op' (just (o' , i')) p with decₛ op op'
    ↓↓ₑ-⊑ₒ-act₁-aux {o} {i} op .op (just (o' , i')) p | yes refl =
      ↓↓ₑ-⊑ₒ-act₁-≡ op p
    ↓↓ₑ-⊑ₒ-act₁-aux {o} {i} op op' (just (o' , i')) p | no ¬q =
      ↓↓ₑ-⊑ₒ-act₁-≢ op op' ¬q p 


-- ENVELOPING THE EFFECT ANNOTATION REDUCTION WITH MLTIPLE INTERRUPT ACTIONS

{- LEMMA 4.6 -}

{- 
   For time being, we postulate this lemma in Agda, but include a paper proof below.
-}

postulate
  ↓↓ₑ-⊑ₒ-act : {o : O}
               {i : I} → 
               (ops : List Σₛ) →
               (op : Σₛ) →
               ----------------------------------------------------------
               proj₁ (ops ↓↓ₑ (o , i)) ⊑ₒ proj₁ (ops ↓↓ₑ (op ↓ₑ (o , i)))

{-

Paper proof for ↓↓ₑ-⊑ₒ-act:

We proceed by case analysis on i op:

1) If i op = nothing 

   Then op ↓ₑ (o , i) = (o , i), thus inclusion holds trivially by reflexivity.

2) If i op = just (o' , i')

   Then op ↓ₑ (o , i) = (o ∪ o' , i[ op ↦ nothing ] ∪ i'), and we need to prove

     proj₁ (ops ↓↓ₑ (o , i)) ⊑ proj₁ (ops ↓↓ₑ (o ∪ o' , i[ op ↦ nothing ] ∪ i')).

  Next, we note that (without loss of generality, we consider i op = nothing 
  to be the same as i op = (o' , i') where o' and i' are empty maps)

    proj₁ ((opₙ :: ... :: op₁ :: []) ↓↓ₑ (o , i))
    =
    proj₁ (opₙ ↓ₑ (... (op₂ ↓ₑ (op₁ ↓ₑ (o , i)))))
    =
    proj₁ (opₙ ↓ₑ (... (op₂ ↓ₑ (o ∪ o₁ , i[ op₁ ↦ nothing ] ∪ i₁))))             (assuming that i op₁ = (o₁ , i₁))
    =
    (o ∪ o₁ ∪ o₂ ∪ ... ∪ oₙ)    

    where 

      (oᵢ , iᵢ) = ((i[ op₁ ↦ nothing , ... , opᵢ₋₁ ↦ nothing ] 
                    ∪ 
                    i₁[ op₂ ↦ nothing , ... , opᵢ₋₁ ↦ nothing ]
                    ∪
                    i₂[ op₃ ↦ nothing , ... , opᵢ₋₁ ↦ nothing ]
                    ∪
                    ...
                    ∪
                    ...
                    ∪
                    iᵢ₋₁) opᵢ)

  and

    proj₁ (ops ↓↓ₑ (o ∪ o' , i[ op ↦ nothing ] ∪ i')) 
    = 
    (o ∪ o' ∪ o₁' ∪ ... ∪ oₙ')

  where 

    (oᵢ' , iᵢ') = ((i[ op ↦ nothing , op₁ ↦ nothing , ... , opᵢ₋₁ ↦ nothing ] 
                    ∪ 
                    i'[ op₁ ↦ nothing , ... , opᵢ₋₁ ↦ nothing ] 
                    ∪
                    i₁'[ op₂ ↦ nothing , ... , opᵢ₋₁ ↦ nothing ]
                    ∪
                    i₂'[ op₃ ↦ nothing , ... , opᵢ₋₁ ↦ nothing ]
                    ∪
                    ...
                    ∪
                    ...
                    ∪
                    iᵢ₋₁') opᵢ)

  Thus we need to show

    o ∪ o₁ ∪ o₂ ∪ ... ∪ oₙ ⊑ o ∪ o' ∪ o₁' ∪ ... ∪ oₙ'

  For which it suffices to show (by using the idempotency of ∪ on RHS with o' repeatedly)

    oᵢ ⊑ o' ∪ oᵢ'

  The importance of including o' in the right-hand side will become apparent towards the end.

  We proceed by induction on n, i.e., the length of the list ops.

    2.1) If n = length ops = 0:

         Then we are done vacuously (and the overall inclusion is just o ⊑ o ∪ o').

    2.2) If n = length ops = m + 1

         By induction hypothesis, we know that for all 1 <= i <= m, we have
        
           oᵢ ⊑ o' ∪ oᵢ'

         and we need to show

           oₘ₊₁ ⊑ o' ∪ oₘ₊₁'

         Which, when we unfold the definitions, amounts to having to show

           oₘ₊₁  = proj₁ ((i[ op₁ ↦ nothing , ... , opₘ ↦ nothing ] 
                           ∪ 
                           i₁[ op₂ ↦ nothing , ... , opₘ ↦ nothing ]
                           ∪
                           i₂[ op₃ ↦ nothing , ... , opₘ ↦ nothing ]
                           ∪
                           ...
                           ∪
                           ...
                           ∪
                           iₘ) opₘ₊₁)
           ⊑ 
           o' ∪ oₘ₊₁' = o' ∪ proj₁ ((i[ op ↦ nothing , op₁ ↦ nothing , ... , opₘ ↦ nothing ] 
                                     ∪ 
                                     i'[ op₁ ↦ nothing , ... , opₘ ↦ nothing ] 
                                     ∪
                                     i₁'[ op₂ ↦ nothing , ... , opₘ ↦ nothing ]
                                     ∪
                                     i₂'[ op₃ ↦ nothing , ... , opₘ ↦ nothing ]
                                     ∪
                                     ...
                                     ∪
                                     ...
                                     ∪
                                     iₘ') opₘ₊₁)

         that is

           oₘ₊₁  = proj₁ (i[ op₁ ↦ nothing , ... , opₘ ↦ nothing ] opₘ₊₁)
                   ∪ 
                   proj₁ (i₁[ op₂ ↦ nothing , ... , opₘ ↦ nothing ] opₘ₊₁)
                   ∪
                   proj₁ (i₂[ op₃ ↦ nothing , ... , opₘ ↦ nothing ] opₘ₊₁)
                   ∪
                   ...
                   ∪
                   ...
                   ∪
                   proj₁ (iₘ opₘ₊₁)
           ⊑ 
           o' ∪ oₘ₊₁' = o' ∪ proj₁ (i[ op ↦ nothing , op₁ ↦ nothing , ... , opₘ ↦ nothing ] opₘ₊₁)
                             ∪
                             proj₁ (i'[ op₁ ↦ nothing , ... , opₘ ↦ nothing ] opₘ₊₁)
                             ∪
                             proj₁ (i₁'[ op₂ ↦ nothing , ... , opₘ ↦ nothing ] opₘ₊₁)
                             ∪
                             proj₁ (i₂'[ op₃ ↦ nothing , ... , opₘ ↦ nothing ] opₘ₊₁)
                             ∪
                             ...
                             ∪
                             ...
                             ∪
                             proj₁ (iₘ' opₘ₊₁)

        We prooceed by case analysis whether opₘ₊₁ equals any of the previous opₖs:

        2.2.1) If opₘ₊₁ ≡ opₖ for some 1 <= k <= m

               Then we can peel off the layers k + 1 ... m because opₖ ↦ nothing in those,
               on both sides of the inequality, and we are left having to show 

                 proj₁ (iₖ opₖ) ⊑ o' ∪ proj₁ (iₖ' opₖ)

               and when unfolding iₖ and iₖ' once more, we see that we are left having to show

                 oₖ ⊑ o' ∪ oₖ'

               but this follows directly from the induction hypothesis.

        2.2.2) If opₘ₊₁ ≢ opₖ for none of the 1 <= k <= m

               Then the recursive structure on both sides of the inequality collapses because

                 iₖ[ opₖ₊₁ ↦ nothing , ... , opₘ ↦ nothing ] opₘ₊₁ = iₖ opₘ₊₁

               and similarly for the iₖ's. 

               Thus (after repeatedly using the idempotency of ∪) we are left having to simply show

                 proj₁ (i opₘ₊₁) ⊑ o' ∪ proj₁ ((i[ op ↦ nothing ] ∪ i') opₘ₊₁)

               We proceed by case analysis whether op ≡ opₘ₊₁.

               2.2.2.1) If op ≡ opₘ₊₁:

                        Then we have to show

                          proj₁ (i op) = o'
                          ⊑ 
                          o' ∪ proj₁ ((i[ op ↦ nothing ] ∪ i') op)

                        which holds straightforwardly.

               2.2.2.2) If op ≢ op₁:

                        Then we have to show
               
                          proj₁ (i opₘ₊₁)
                          ⊑
                          o' ∪ proj₁ ((i[ op ↦ nothing ] ∪ i') opₘ₊₁) 
                          = 
                          o' ∪ proj₁ (i[ op ↦ nothing ] opₘ₊₁) ∪ proj₁ (i' opₘ₊₁)
                          =
                          o' ∪ proj₁ (i opₘ₊₁) ∪ proj₁ (i' opₘ₊₁)

                        which also holds straigthforwardly.

               Observe that 2.2.2.1 demonstrates the need to include o' in the inductive argument.

qed.

-}
