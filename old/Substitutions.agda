open import Data.Bool
open import Data.Nat
open import Data.Unit

open import Operations
open import Terms
open import Types
open import TypeSystem

module Substitutions where

mutual 
  up-shift-v : ℕ → VTerm → VTerm
  up-shift-v max (` x) with x <ᵇ max
  ... | true  =
    ` x
  ... | false =
    ` (suc x)
  up-shift-v max ∣ c ∣ =
    ∣ c ∣
  up-shift-v max (ƛ m) =
    ƛ (up-shift-c (suc max) m)
  up-shift-v max ⟨ v ⟩ =
    ⟨ up-shift-v max v ⟩

  up-shift-c : ℕ → CTerm → CTerm
  up-shift-c max (return v) =
    return (up-shift-v max v)
  up-shift-c max (`let m `in n) =
    `let up-shift-c max m `in up-shift-c (suc max) n
  up-shift-c max (v · w) =
    up-shift-v max v · up-shift-v max w
  up-shift-c max (↑ op v m) =
    ↑ op (up-shift-v max v) (up-shift-c max m)
  up-shift-c max (↓ op v m) =
    ↓ op (up-shift-v max v) (up-shift-c max m)
  up-shift-c max (promise op ↦ m `as X `in n) =
    promise op ↦ up-shift-c (suc max) m `as X `in up-shift-c (suc max) n
  up-shift-c max (await v until m) =
    await up-shift-v max v until up-shift-c (suc max) m


mutual
  _[_/_]v : VTerm → VTerm → ℕ → VTerm
  ` y [ w / x ]v with x ≡ᵇ y
  ... | true =
    w
  ... | false =
    ` y
  ∣ c ∣ [ w / x ]v =
    ∣ c ∣
  ƛ m [ w / x ]v =
    ƛ (m [ up-shift-v 0 w / suc x ]c)
  ⟨ v ⟩ [ w / x ]v =
    ⟨ v [ w / x ]v ⟩

  _[_/_]c : CTerm → VTerm → ℕ → CTerm
  return v [ w / x ]c =
    return (v [ w / x ]v)
  (`let m `in n) [ w / x ]c =
    `let m [ w / x ]c `in (n [ up-shift-v 0 w / suc x ]c)
  (v · v') [ w / x ]c =
    (v [ w / x ]v) · (v' [ w / x ]v)
  ↑ op v m [ w / x ]c =
    ↑ op (v [ w / x ]v) (m [ w / x ]c)
  ↓ op v m [ w / x ]c =
    ↓ op (v [ w / x ]v) (m [ w / x ]c)
  (promise op ↦ m `as X `in n) [ w / x ]c =
    promise op ↦ m [ up-shift-v 0 w / suc x ]c `as X `in (n [ up-shift-v 0 w / suc x ]c)
  (await v until m) [ w / x ]c =
    await v [ w / x ]v until (m [ up-shift-v 0 w / suc x ]c)


