open import Data.Nat

open import Operations
open import Types

module Terms where

postulate arₒ : Σₒ → GType -- arity assignment to outgoing signals
postulate arᵢ : Σᵢ → GType  -- arity assignment to incoming interrupts

postulate Σ : Set        -- set of ground constants
postulate ar : Σ → GType -- arity assignment to ground constants

mutual
  data VTerm : Set where
    `   : ℕ → VTerm
    ∣_∣ : Σ → VTerm
    ƛ   : CTerm → VTerm
    ⟨_⟩ : VTerm → VTerm

  data CTerm : Set where
    return             : VTerm → CTerm
    `let_`in_          : CTerm → CTerm → CTerm
    _·_                : VTerm → VTerm → CTerm
    ↑                  : Σₒ → VTerm → CTerm → CTerm
    ↓                  : Σᵢ → VTerm → CTerm → CTerm
    promise_↦_`as_`in_ : Σᵢ → CTerm → VType → CTerm → CTerm
    await_until_       : VTerm → CTerm → CTerm
    
