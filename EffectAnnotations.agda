open import Data.Bool hiding (if_then_else_)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality)
open import Relation.Nullary
open import Relation.Nullary.Negation

module EffectAnnotations where

open import Axiom.Extensionality.Propositional
postulate ext : ∀ {a b} → Extensionality a b                -- assuming function extensionality (for the rest of the development)

-- SIGNAL AND INTERRUPT NAMES

postulate Σₒ : Set                                           -- set of incoming signal names
postulate Σᵢ : Set                                           -- set of outgoing interrupt names

postulate decᵢ : (op op' : Σᵢ) → Dec (op ≡ op')               -- interrupt names have decidable equality

if'_then_else_ : {A : Set} {op op' : Σᵢ} → Dec (op ≡ op') → A → A → A
if' yes p then x else y = x
if' no ¬p then x else y = y

if_≡_then_else_ : {A : Set} → Σᵢ → Σᵢ → A → A → A
if op ≡ op' then x else y =
  if' (decᵢ op op') then x else y


-- EFFECT ANNOTATIONS

mutual
  data O : Set where                                         -- set of effect annotations of outgoing signals
    omap : (Σₒ → Maybe ⊤) → O

  data I : Set where                                         -- set of effect annotations of incoming interrupts
    imap : (Σᵢ → Maybe (O × I)) → I


-- DECIDABLE EQUALITY OF SIGNAL EFFECT ANNOTATIONS

dec-⊤ : (t u : ⊤) → Dec (t ≡ u)
dec-⊤ tt tt = yes refl

inj-just : {X : Set} {x y : X} → just x ≡ just y → x ≡ y
inj-just refl = refl
  
dec-maybe : {X : Set} → ((x y : X) → Dec (x ≡ y)) → (m m' : Maybe X) → Dec (m ≡ m')
dec-maybe p nothing nothing =
  yes refl
dec-maybe p nothing (just x) =
  no (λ ())
dec-maybe p (just x) nothing =
  no (λ ())
dec-maybe p (just x) (just y) with p x y
... | yes refl =
  yes refl
... | no ¬q =
  no (λ r → contradiction (inj-just r) ¬q)


postulate dec-ext : {X Y : Set} → (f g : X → Y) → ((x : X) → Dec (f x ≡ g x)) → Dec (f ≡ g)


dec-effₒ : (o o' : O) → Dec (o ≡ o')
dec-effₒ (omap o) (omap o') with dec-ext o o' (λ op → dec-maybe dec-⊤ (o op) (o' op))
... | yes refl =
  yes refl
... | no ¬p =
  no (λ q → contradiction (inj-omap q) ¬p)

  where
    inj-omap : {o o' : Σₒ → Maybe ⊤} → omap o ≡ omap o' → o ≡ o'
    inj-omap refl = refl


-- DECIDABLE EQUALITY OF INTERRUPT EFFECT ANNOTATIONS

mutual 
  inj-pair₁ : {X Y : Set} {x x' : X} {y y' : Y} → (x , y) ≡ (x' , y') → x ≡ x'
  inj-pair₁ refl = refl

  inj-pair₂ : {X Y : Set} {x x' : X} {y y' : Y} → (x , y) ≡ (x' , y') → y ≡ y'
  inj-pair₂ refl = refl

  dec-effᵢ-aux : (m m' : Maybe (O × I)) → Dec (m ≡ m')
  dec-effᵢ-aux nothing nothing =
    yes refl
  dec-effᵢ-aux nothing (just (o' , i')) =
    no (λ ())
  dec-effᵢ-aux (just (o , i)) nothing =
    no (λ ())
  dec-effᵢ-aux (just (o , i)) (just (o' , i')) with dec-effₒ o o' | dec-effᵢ i i'
  ... | yes refl | yes refl =
    yes refl
  ... | yes refl | no ¬q =
    no (λ r → contradiction (inj-pair₂ (inj-just r)) ¬q)
  ... | no ¬p | _ =
    no (λ q → contradiction (inj-pair₁ (inj-just q)) ¬p)

  dec-effᵢ : (i i' : I) → Dec (i ≡ i')
  dec-effᵢ (imap i) (imap i') with dec-ext i i' (λ op → dec-effᵢ-aux (i op) (i' op))
  ... | yes refl =
    yes refl
  ... | no ¬p =
    no (λ q → contradiction (inj-imap q) ¬p)

    where
      inj-imap : {i i' : Σᵢ → Maybe (O × I)} → imap i ≡ imap i' → i ≡ i'
      inj-imap refl = refl



-- UNION OF EFFECT ANNOTATIONS

∪ₒ-aux' : (o o' : Maybe ⊤) → Maybe ⊤
∪ₒ-aux' nothing o' = o'
∪ₒ-aux' (just tt) o' = just tt
  
∪ₒ-aux : (o o' : Σₒ → Maybe ⊤) → Σₒ → Maybe ⊤
∪ₒ-aux o o' op =
  ∪ₒ-aux' (o op) (o' op)

_∪ₒ_ : O → O → O
(omap o) ∪ₒ (omap o') =
  omap (∪ₒ-aux o o')


mutual

  ∪ᵢ-aux : (i i' : Σᵢ → Maybe (O × I)) → Σᵢ → Maybe (O × I)
  ∪ᵢ-aux i i' op =
    ∪ᵢ-aux' (i op) (i' op)

  ∪ᵢ-aux' : (oi oi' : Maybe (O × I)) → Maybe (O × I)
  ∪ᵢ-aux' nothing nothing =
    nothing
  ∪ᵢ-aux' nothing (just oi''') =
    just oi'''
  ∪ᵢ-aux' (just oi'') nothing =
    just oi''
  ∪ᵢ-aux' (just (o'' , (imap i''))) (just (o''' , (imap i'''))) =
    just (o'' ∪ₒ o''' , imap (∪ᵢ-aux i'' i'''))

_∪ᵢ_ : I → I → I
(imap i) ∪ᵢ (imap i') =
  imap (∪ᵢ-aux i i')


-- SETTING THE VALUE OF EFFECT ANNOTATION AT AN INTERRUPT

_[_↦_]ᵢ : I → Σᵢ → Maybe (O × I) → I
(imap i) [ op ↦ v ]ᵢ =
  imap λ op' → if op ≡ op' then v else i op'


-- ACTION OF INTERRUPTS ON EFFECT ANNOTATIONS

infix 40 _↓ₑ_

↓ₑ-aux : Σᵢ → Maybe (O × I) → O × I → O × I
↓ₑ-aux op nothing (o , i) =
  (o , i)
↓ₑ-aux op (just (o' , i')) (o , i) =
  (o ∪ₒ o') , ((i [ op ↦ nothing ]ᵢ) ∪ᵢ i')

_↓ₑ_ : Σᵢ → O × I → O × I
op ↓ₑ (omap o , imap i) =
  ↓ₑ-aux op (i (op)) (omap o , imap i)


-- CHECKING THE CONTENTS OF EFFECT ANNOTATIONS

_∈ₒ_ : Σₒ → O → Set
op ∈ₒ (omap o) =
  o op ≡ just tt


lkpᵢ : Σᵢ → I → Maybe (O × I)
lkpᵢ op (imap i) = i op


-- SUBTYPING RELATIONS FOR EFFECT ANNOTATIONS

_⊑ₒ_ : O → O → Set
o ⊑ₒ o' = (op : Σₒ) → op ∈ₒ o → op ∈ₒ o'

data _⊑ᵢ_ (i i' : I) : Set where
  rel : ((op : Σᵢ) → {o : O} → {i'' : I} → lkpᵢ op i ≡ just (o , i'') →
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
                  {o' : O} {i' : Σᵢ → Maybe (O × I)} →
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
    ⊑ᵢ-trans-aux' : (o : O) → (j : I) → (op : Σᵢ) →
                    (o' : O) → (j' : I) → lkpᵢ op i' ≡ just (o' , j') → (o ⊑ₒ o') → (j ⊑ᵢ j') →
                    Σ[ o'' ∈ O ] Σ[ j'' ∈ I ] (lkpᵢ op i'' ≡ just (o'' , j'') × (o' ⊑ₒ o'') × (j' ⊑ᵢ j'')) →
                    Σ[ o'' ∈ O ] Σ[ j'' ∈ I ] (lkpᵢ op i'' ≡ just (o'' , j'') × (o ⊑ₒ o'') × (j ⊑ᵢ j''))
    ⊑ᵢ-trans-aux' o j op o' j' r' s t (o'' , j'' , r'' , s' , t') =
      o'' , j'' , r'' , ⊑ₒ-trans s s' , ⊑ᵢ-trans t t'

    ⊑ᵢ-trans-aux : (o : O) → (j : I) → (op : Σᵢ) →
                    Σ[ o' ∈ O ] Σ[ j' ∈ I ] (lkpᵢ op i' ≡ just (o' , j') × (o ⊑ₒ o') × (j ⊑ᵢ j')) →
                    Σ[ o'' ∈ O ] Σ[ j'' ∈ I ] (lkpᵢ op i'' ≡ just (o'' , j'') × (o ⊑ₒ o'') × (j ⊑ᵢ j''))
    ⊑ᵢ-trans-aux o j op (o' , j' , r' , s , t) =
      ⊑ᵢ-trans-aux' o j op o' j' r' s t (q op r')



-- LEFT AND RIGHT INCLUSIONS INTO UNIONS OF EFFECT ANNOTATIONS

⊑ₒ-inl : {o o' : O} →
         -------------
         o ⊑ₒ (o ∪ₒ o')

⊑ₒ-inl {omap o} {omap o'} op with o op | o' op
... | nothing | nothing = λ p → p
... | nothing | just tt = λ _ → refl
... | just tt | nothing = λ p → p
... | just tt | just tt = λ p → p


⊑ₒ-inr : {o o' : O} →
         -------------
         o' ⊑ₒ (o ∪ₒ o')

⊑ₒ-inr {omap o} {omap o'} op with o op | o' op
... | nothing | nothing = λ p → p
... | nothing | just tt = λ p → p
... | just tt | nothing = λ _ → refl
... | just tt | just tt = λ p → p


⊑ᵢ-inl : {i i' : I} →
        -------------
        i ⊑ᵢ (i ∪ᵢ i')

⊑ᵢ-inl {imap i} {imap i'} =
  rel (λ op → ⊑ᵢ-inl-aux (i op) (i' op))

  where
    ⊑ᵢ-inl-aux : (oi oi' : Maybe (O × I)) →
                 {o : O} {i'' : I} →
                 oi ≡ just (o , i'') →
                 Σ[ o' ∈ O ] Σ[ i''' ∈ I ] (∪ᵢ-aux' oi oi' ≡ just (o' , i''') × (o ⊑ₒ o') × (i'' ⊑ᵢ i'''))
    ⊑ᵢ-inl-aux (just .(o , i'')) nothing {o} {i''} refl =
      o , i'' , refl , ⊑ₒ-refl , ⊑ᵢ-refl
    ⊑ᵢ-inl-aux (just .(o , imap i'')) (just (o' , imap i''')) {o} {imap i''} refl =
      o ∪ₒ o' , imap (∪ᵢ-aux i'' i''') , refl , ⊑ₒ-inl , ⊑ᵢ-inl


⊑ᵢ-inr : {i i' : I} →
        -------------
        i' ⊑ᵢ (i ∪ᵢ i')

⊑ᵢ-inr {imap i} {imap i'} =
  rel (λ op → ⊑ᵢ-inr-aux (i op) (i' op))

  where
    ⊑ᵢ-inr-aux : (oi oi' : Maybe (O × I)) →
                 {o : O} {i'' : I} →
                 oi' ≡ just (o , i'') →
                 Σ[ o' ∈ O ] Σ[ i''' ∈ I ] (∪ᵢ-aux' oi oi' ≡ just (o' , i''') × (o ⊑ₒ o') × (i'' ⊑ᵢ i'''))
    ⊑ᵢ-inr-aux nothing (just .(o , i'')) {o} {i''} refl =
      o , i'' , refl , ⊑ₒ-refl , ⊑ᵢ-refl
    ⊑ᵢ-inr-aux (just (o' , imap i''')) (just .(o , imap i'')) {o} {imap i''} refl =
      o' ∪ₒ o , imap (∪ᵢ-aux i''' i'') , refl , ⊑ₒ-inr , ⊑ᵢ-inr


-- INCLUSION INTO ACTED UPON EFFECT ANNOTATION

opₒ-in-∪ₒ-lem : {o o' : O}
               {op : Σₒ} →
               op ∈ₒ o →
               --------------
               op ∈ₒ (o ∪ₒ o')

opₒ-in-∪ₒ-lem {omap o} {omap o'} {op} p with o (op)
opₒ-in-∪ₒ-lem {omap o} {omap o'} {op} refl | just .tt = refl


opₒ-in-↓ₑ-lem : {o : O}
               {i : I}
               {op : Σᵢ}
               {op' : Σₒ} →
               op' ∈ₒ o →
               ---------------------------
               op' ∈ₒ proj₁ (op ↓ₑ (o , i))
               
opₒ-in-↓ₑ-lem {omap o} {imap i} {op} {op'} p with i (op)
... | nothing = p
... | just (o' , i') = ⊑ₒ-inl op' p


⊑ₒ-↓ₑ-o-lem : {o o' : O}
             {i i' : I}
             {op : Σᵢ} → 
             lkpᵢ op i ≡ just (o' , i') → 
             ---------------------------
             o ⊑ₒ proj₁ (op ↓ₑ (o , i))
             
⊑ₒ-↓ₑ-o-lem {omap o} {omap o'} {imap i} {imap i'} {op} p with i (op)
⊑ₒ-↓ₑ-o-lem {omap o} {omap o'} {imap i} {imap i'} {op} refl | just .(omap o' , imap i') =
  ⊑ₒ-↓ₑ-o-lem-aux       

  where
    ⊑ₒ-↓ₑ-o-lem-aux : (op' : Σₒ) → o op' ≡ just tt → ∪ₒ-aux o o' op' ≡ just tt
    ⊑ₒ-↓ₑ-o-lem-aux op' p with o op'
    ⊑ₒ-↓ₑ-o-lem-aux op' p | just tt = refl

⊑ₒ-↓ₑ-o'-lem : {o o' : O}
              {i i' : I}
              {op : Σᵢ} → 
              lkpᵢ op i ≡ just (o' , i') → 
              ---------------------------
              o' ⊑ₒ proj₁ (op ↓ₑ (o , i))

⊑ₒ-↓ₑ-o'-lem {omap o} {omap o'} {imap i} {imap i'} {op} p with i (op)
⊑ₒ-↓ₑ-o'-lem {omap o} {omap o'} {imap i} {imap i'} {op} refl | just .(omap o' , imap i') =
  ⊑ₒ-↓ₑ-o'-lem-aux

  where
    ⊑ₒ-↓ₑ-o'-lem-aux : (op' : Σₒ) → o' op' ≡ just tt → ∪ₒ-aux o o' op' ≡ just tt
    ⊑ₒ-↓ₑ-o'-lem-aux op' p with o op'
    ⊑ₒ-↓ₑ-o'-lem-aux op' p | nothing = p
    ⊑ₒ-↓ₑ-o'-lem-aux op' p | just tt = refl

⊑ᵢ-↓ₑ-i'-lem : {o o' : O}
              {i i' : I}
              {op : Σᵢ} → 
              lkpᵢ op i ≡ just (o' , i') → 
              ---------------------------
              i' ⊑ᵢ proj₂ (op ↓ₑ (o , i))

⊑ᵢ-↓ₑ-i'-lem {omap o} {omap o'} {imap i} {imap i'} {op} p with i (op)
⊑ᵢ-↓ₑ-i'-lem {omap o} {omap o'} {imap i} {imap i'} {op} refl | just .(omap o' , imap i') =
  rel ⊑ᵢ-↓ₑ-i'-lem-aux

  where
    ⊑ᵢ-↓ₑ-i'-lem-aux : (op' : Σᵢ) {o'' : O} {i'' : I} →
      i' op' ≡ just (o'' , i'') →
      Σ[ o''' ∈ O ] Σ[ i''' ∈ I ] (∪ᵢ-aux (λ op' → if op ≡ op' then nothing else i op') i' op' ≡ just (o''' , i''') ×
                                  (o'' ⊑ₒ o''') × (i'' ⊑ᵢ i'''))
    ⊑ᵢ-↓ₑ-i'-lem-aux op' {o''} {i''} p with decᵢ op op'
    ⊑ᵢ-↓ₑ-i'-lem-aux op' {o''} {i''} p | yes refl with i' (op)
    ⊑ᵢ-↓ₑ-i'-lem-aux op' {o''} {i''} refl | yes refl | just .(o'' , i'') =
      o'' , (i'' , refl , (⊑ₒ-refl , ⊑ᵢ-refl))
    ⊑ᵢ-↓ₑ-i'-lem-aux op' {o''} {i''} p | no ¬q with i (op') | i' (op') 
    ⊑ᵢ-↓ₑ-i'-lem-aux op' {o''} {i''} refl | no ¬q | nothing | just .(o'' , i'') =
      o'' , (i'' , refl , (⊑ₒ-refl , ⊑ᵢ-refl))
    ⊑ᵢ-↓ₑ-i'-lem-aux op' {o''} {imap i''} refl | no ¬q | just (o''' , (imap i''')) | just .(o'' , (imap i'')) =
      (o''' ∪ₒ o'') , (imap (∪ᵢ-aux i''' i'') , (refl , (⊑ₒ-inr , ⊑ᵢ-inr)))


-- EFFECT ANNOTATION OF AN INTERRUPT THAT WAS NOT ACTED WITH

lkpᵢ-↓ₑ-neq : {o o' : O} {i i' : I} {op op' : Σᵢ} → ¬ op ≡ op' → lkpᵢ op' i ≡ just (o' , i') →
             Σ[ o'' ∈ O ] Σ[ i'' ∈ I ] (lkpᵢ op' (proj₂ (op ↓ₑ (o , i))) ≡ just (o'' , i'') × o' ⊑ₒ o'' × i' ⊑ᵢ i'')
lkpᵢ-↓ₑ-neq {omap o} {o'} {imap i} {imap i'} {op} {op'} p q with i (op)
... | nothing =
  o' , imap i' , q , ⊑ₒ-refl , ⊑ᵢ-refl
lkpᵢ-↓ₑ-neq {omap o} {o'} {imap i} {imap i'} {op} {op'} p q | just (o'' , imap i'') with decᵢ op op'
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
  (o''' ∪ₒ o'''') , (imap i''') ∪ᵢ (imap i'''') , refl , ⊑ₒ-inl , ⊑ᵢ-inl


-- NEXT DEFINED EFFECT ANNOTATION UNDER SUBTYPING EFFECT ANNOTATIONS

lkpᵢ-nextₒ : {o'' : O} {i i' i'' : I} {op : Σᵢ} →
            i ⊑ᵢ i' → lkpᵢ op i ≡ just (o'' , i'') → O
            
lkpᵢ-nextₒ {o''} {i} {i'} {i''} {op} (rel p) q =
  proj₁ (p op q)


lkpᵢ-nextᵢ : {o'' : O} {i i' i'' : I} {op : Σᵢ} →
            i ⊑ᵢ i' → lkpᵢ op i ≡ just (o'' , i'') → I

lkpᵢ-nextᵢ {o''} {i} {i'} {i''} {op} (rel p) q =
  proj₁ (proj₂ (p op q))


lkpᵢ-next-eq : {o'' : O} {i i' i'' : I} {op : Σᵢ} →
              (p : i ⊑ᵢ i') →
              (q : lkpᵢ op i ≡ just (o'' , i'')) →
              ------------------------------------------------
              lkpᵢ op i' ≡ just (lkpᵢ-nextₒ p q , lkpᵢ-nextᵢ p q)

lkpᵢ-next-eq {o''} {i} {i'} {i''} {op} (rel p) q =
  proj₁ (proj₂ (proj₂ (p op q)))


lkpᵢ-next-⊑ₒ : {o'' : O} {i i' i'' : I} {op : Σᵢ} →
              (p : i ⊑ᵢ i') →
              (q : lkpᵢ op i ≡ just (o'' , i'')) →
              -----------------------------------
              o'' ⊑ₒ lkpᵢ-nextₒ p q

lkpᵢ-next-⊑ₒ {o''} {i} {i'} {i''} {op} (rel p) q =
  proj₁ (proj₂ (proj₂ (proj₂ (p op q))))


lkpᵢ-next-⊑ᵢ : {o'' : O} {i i' i'' : I} {op : Σᵢ} →
              (p : i ⊑ᵢ i') →
              (q : lkpᵢ op i ≡ just (o'' , i'')) →
              -----------------------------------
              i'' ⊑ᵢ lkpᵢ-nextᵢ p q

lkpᵢ-next-⊑ᵢ {o''} {i} {i'} {i''} {op} (rel p) q =
  proj₂ (proj₂ (proj₂ (proj₂ (p op q))))

