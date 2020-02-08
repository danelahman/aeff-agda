open import Data.Bool hiding (if_then_else_)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module Operations where

postulate Σₒ : Set                                           -- set of incoming signal names
postulate Σᵢ : Set                                           -- set of outgoing interrupt names

postulate decᵢ : (op op' : Σᵢ) → Dec (op ≡ op')               -- decidable equality for interrupt names

if_≡_then_else_ : {A : Set} → Σᵢ → Σᵢ → A → A → A
if op ≡ op' then x else y with decᵢ op op'
... | yes p = x
... | no ¬p = y

mutual

  data O : Set where                                         -- set of effect annotations of outgoing signals
    omap : (Σₒ → Bool) → O

  data I : Set where                                         -- set of effect annotations of incoming interrupts
    imap : (Σᵢ → Maybe (O × I)) → I

_∈ₒ_ : Σₒ → O → Set
op ∈ₒ (omap o) = T (o op)

lkpᵢ : Σᵢ → I → Maybe (O × I)
lkpᵢ op (imap i) = i op

_[_↦_]ᵢ : I → Σᵢ → Maybe (O × I) → I
(imap i) [ op ↦ v ]ᵢ =
  imap λ op' → if op ≡ op' then v else i op'

_∪ₒ_ : O → O → O
(omap o) ∪ₒ (omap o') =
  omap (λ op → o op ∨ o' op)

{-# TERMINATING #-}                                          -- Just helping Agda out, as it cannot see that i'' is
∪ᵢ-aux : (i i' : Σᵢ → Maybe (O × I)) → Σᵢ → Maybe (O × I)      -- smaller than i' (op) when i' (op) = just (o'' , i'').
∪ᵢ-aux i i' op with i (op) | i' (op)
... | nothing          | nothing =
  nothing
... | nothing          | just (o''' , i''') =
  just (o''' , i''')
... | just (o'' , i'') | nothing =
  just (o'' , i'')
... | just (o'' , (imap i'')) | just (o''' , (imap i''')) =
  just (o'' ∪ₒ o''' , imap (∪ᵢ-aux i'' i'''))

_∪ᵢ_ : I → I → I
(imap i) ∪ᵢ (imap i') =
  imap (λ op → ∪ᵢ-aux i i' op)

infix 40 _↓ₑ_

_↓ₑ_ : Σᵢ → O × I → O × I
op ↓ₑ (omap o , imap i) with i (op)
... | nothing =
  (omap o , imap i)
... | just (o' , i') =
  ((omap o) ∪ₒ o') , (((imap i) [ op ↦ nothing ]ᵢ) ∪ᵢ i')
