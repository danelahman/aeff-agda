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
    var     : ℕ → VTerm
    const   : Σ → VTerm
    lam     : CTerm → VTerm
    promise : VTerm → VTerm

  data CTerm : Set where
    return    : VTerm → CTerm
    let-in    : CTerm → CTerm → CTerm
    apply     : VTerm → VTerm → CTerm
    signal    : Σₒ → VTerm → CTerm → CTerm
    interrupt : Σᵢ → VTerm → CTerm → CTerm
    promise   : Σᵢ → CTerm → VType → CTerm → CTerm
    await     : VTerm → CTerm → CTerm
    
