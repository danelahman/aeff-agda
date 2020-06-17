open import Data.Empty
open import Data.List renaming (_∷_ to _∷ₗ_ ; [_] to [_]ₗ)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
open import AwaitingComputations
open import EffectAnnotations
open import Preservation
open import ProcessPreservation
open import Progress
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module ProcessProgress where

-- PROCESS RESULTS

data ParResult⟨_⟩ : {o : O} {PP : PType o} → [] ⊢P⦂ PP → Set where

  run    : {X : VType}
           {o : O}
           {i : I} → 
           {M : [] ⊢M⦂ X ! (o , i)} →
           RunResult⟨ [] ∣ M ⟩ →
           --------------------------
           ParResult⟨ run M ⟩

  par    : {o o' : O}
           {PP : PType o}
           {QQ : PType o'}
           {P : [] ⊢P⦂ PP}
           {Q : [] ⊢P⦂ QQ} →
           ParResult⟨ P ⟩ →
           ParResult⟨ Q ⟩ →
           ------------------
           ParResult⟨ P ∥ Q ⟩

data ProcResult⟨_⟩ : {o : O} {PP : PType o} → [] ⊢P⦂ PP → Set where

  proc   : {o : O}
           {PP : PType o}
           {P : [] ⊢P⦂ PP} →
           ParResult⟨ P ⟩ →
           -----------------
           ProcResult⟨ P ⟩

  signal : {o : O}
           {PP : PType o}
           {op : Σₛ}
           {p : op ∈ₒ o}
           {V : [] ⊢V⦂ ``(payload op)}
           {P : [] ⊢P⦂ PP} →
           ProcResult⟨ P ⟩ →
           ---------------------------
           ProcResult⟨ ↑ op p V P ⟩


-- PROGRESS THEOREM FOR PROCESSES

{- THEOREM 4.3 -}

proc-progress : {o : O}
                {PP : PType o} →
                (P : [] ⊢P⦂ PP) →
                -------------------------------------------------------------------------------
                (Σ[ o' ∈ O ] Σ[ QQ ∈ PType o' ] Σ[ r ∈ PP ⇝ QQ ] Σ[ Q ∈ [] ⊢P⦂ QQ ] (P [ r ]↝ Q)
                 ⊎
                 ProcResult⟨ P ⟩)

proc-progress (run {X} {o} {i} M) with progress M
... | inj₁ (M' , r) =
  inj₁ (_ , _ , _ , _ , run r)
... | inj₂ (comp R) =
  inj₂ (proc (run R))
... | inj₂ (signal {_} {_} {_} {_} {p} {V} {Q} R) =
  inj₁ (_ , _ , _ , _ , ↑ p V Q)
proc-progress (P ∥ Q) with proc-progress P
... | inj₁ (o' , PP' , r , P' , r') =
  inj₁ (_ , _ , _ , _ , context ([-] ∥ₗ Q) r')
... | inj₂ R with proc-progress Q
... | inj₁ (o' , QQ' , r , Q' , r') =
  inj₁ (_ , _ , _ , _ , context (P ∥ᵣ [-]) r')
proc-progress (P ∥ Q) | inj₂ (proc R) | inj₂ (proc R') =
  inj₂ (proc (par R R'))
proc-progress (P ∥ .(↑ _ _ _ _)) | inj₂ R | inj₂ (signal {_} {_} {_} {p} {V} {Q} R') =
  inj₁ (_ , _ , _ , _ , ↑-∥ᵣ p V P Q)
proc-progress (.(↑ _ _ _ _) ∥ Q) | inj₂ (signal {_} {_} {_} {p} {V} {P} R) | inj₂ R' =
  inj₁ (_ , _ , _ , _ , ↑-∥ₗ p V P Q)
proc-progress (↑ op p V P) with proc-progress P
... | inj₁ (o' , PP' , r , P' , r') =
  inj₁ (_ , _ , _ , _ , context (↑ op p V [-]) r')
... | inj₂ R =
  inj₂ (signal R)
proc-progress (↓ op V P) with proc-progress P
... | inj₁ (o' , OO' , r , P' , r') =
  inj₁ (_ , _ , _ , _ , context (↓ op V [-]) r')
... | inj₂ (proc (run {_} {_} {_} {M} R)) =
  inj₁ (_ , _ , _ , _ , ↓-run V M)
... | inj₂ (proc (par {_} {_} {_} {_} {Q} {Q'} R R')) =
  inj₁ (_ , _ , _ , _ , ↓-∥ V Q Q')
... | inj₂ (signal {_} {_} {_} {p} {W} {Q} R) =
  inj₁ (_ , _ , _ , _ , ↓-↑ p V W Q)
