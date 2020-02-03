open import Data.Nat
open import Data.Unit

open import Operations
open import Terms
open import Types
open import TypeSystem

module Substitutions where

mutual 
  lift-v : VTerm → VTerm
  lift-v (` x) = ` (suc x)
  lift-v ∣ c ∣ = ∣ c ∣
  lift-v (ƛ m) = ƛ {!!}
  lift-v ⟨ v ⟩ = ⟨ lift-v v ⟩

  lift-c : CTerm → CTerm
  lift-c m = {!!}


mutual
  _[_/_]v : VTerm → VTerm → ℕ → VTerm
  ` y [ w / x ]v = {!!}
  ∣ c ∣ [ w / x ]v = ∣ c ∣
  ƛ m [ w / x ]v = {!!}
  ⟨ v ⟩ [ w / x ]v = ⟨ v [ w / x ]v ⟩

  _[_/_]c : CTerm → VTerm → ℕ → CTerm
  m [ v / x ]c = {!!}


