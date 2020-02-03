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
(if op ≡ op' then x else y) | yes p = x
(if op ≡ op' then x else y) | no ¬p = y

mutual

  data O : Set where                                         -- set of effect annotations of outgoing signals
    omap : (Σₒ → Bool) → O

  data I : Set where                                         -- set of effect annotations of incoming interrupts
    imap : (Σᵢ → Maybe (O × I)) → I

_∈ₒ_ : Σₒ → O → Set
op ∈ₒ (omap o) = T (o op)

lkpᵢ : Σᵢ → I → Maybe (O × I)
lkpᵢ op (imap i) = i op

_∪ₒ_ : O → O → O
(omap o) ∪ₒ (omap o') =
  omap (λ op → o op ∨ o' op)

_↓ₒ_ : Σᵢ → O × I → O
op ↓ₒ (omap o , imap i) =
  omap (λ op' → o op' ∨ maybe (λ { (omap o' , imap i) → o' op' }) false (i op))

_↓ᵢ_ : Σᵢ → O × I → I
op ↓ᵢ (omap o , imap i) =
  imap (λ op' → if op ≡ op' then maybe (λ { (omap o' , imap i') → i' op' }) nothing (i op) else i op')

_↓ₑ_ : Σᵢ → O × I → O × I
op ↓ₑ (omap o , imap i) =
  (op ↓ₒ ( omap o , imap i ) , op ↓ᵢ (omap o , imap i))
