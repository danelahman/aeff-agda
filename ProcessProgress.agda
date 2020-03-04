open import Data.Empty
open import Data.List renaming (_∷_ to _∷∷_ ; [_] to ⟦_⟧)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import AEff
open import EffectAnnotations
open import Preservation
open import ProcessPreservation
open import Progress
open import Renamings
open import Substitutions
open import AwaitingComputations
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module ProcessProgress where

-- PROCESS RESULTS

data RunResult⟨_∣_⟩ (Γ : Ctx) : {C : CType} → ⟨⟨ Γ ⟩⟩ ⊢M⦂ C → Set where

  return   : {X : VType}
             {o : O}
             {i : I}
             (V : ⟨⟨ Γ ⟩⟩ ⊢V⦂ X) →
             -----------------------------------------
             RunResult⟨ Γ ∣ return {o = o} {i = i} V ⟩

  promise  : {X Y : VType}
             {o o' : O}
             {i i' : I}
             {op : Σₛ}
             {p : lkpᵢ op i ≡ just (o' , i')}
             {M : ⟨⟨ Γ ⟩⟩ ∷ ``(payload op) ⊢M⦂ ⟨ X ⟩ ! (o' , i')}
             {N : ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)} →
             RunResult⟨ Γ ∷ X ∣ N ⟩ →
             ----------------------------------------------------
             RunResult⟨ Γ ∣ promise op ∣ p ↦ M `in N ⟩

  awaiting : {C : CType}
             {Y : VType}
             {y : ⟨ Y ⟩ ∈ ⟨⟨ Γ ⟩⟩}
             {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
             y ⧗ M →
             ---------------------
             RunResult⟨ Γ ∣ M ⟩


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


data Result⟨_⟩ : {o : O} {PP : PType o} → [] ⊢P⦂ PP → Set where

  proc   : {o : O}
           {PP : PType o}
           {P : [] ⊢P⦂ PP} →
           ParResult⟨ P ⟩ →
           -----------------
           Result⟨ P ⟩

  signal : {o : O}
           {PP : PType o}
           {op : Σₛ}
           {p : op ∈ₒ o}
           {V : [] ⊢V⦂ ``(payload op)}
           {P : [] ⊢P⦂ PP} →
           Result⟨ P ⟩ →
           ---------------------------
           Result⟨ ↑ op p V P ⟩


-- HOISTING A RETURN VALUE IS A RUN RESULT

return-h-runresult : {Γ : Ctx}
                     {Δ : BCtx}
                     {X : VType}
                     {o : O}
                     {i : I}
                     (V : (⟨⟨ Γ ⟩⟩ ⋈ Δ) ⊢V⦂ X) →
                     (H : ⟨⟨ Γ ⟩⟩ ⊢H[ Δ ]⦂ X ! (o , i)) →
                     ------------------------------------
                     RunResult⟨ Γ ∣ H [ return V ]h ⟩

return-h-runresult V [-] =
  return V
return-h-runresult V (promise op ∣ p ↦ M `in H) =
  promise (return-h-runresult V H)


-- HOISTING AN AWAITING COMPUTATION IS A RUN RESULT

await-h-runresult : {Γ : Ctx}
                    {Δ : BCtx}
                    {X Y : VType}
                    {o : O}
                    {i : I} →
                    {y : ⟨ Y ⟩ ∈ (⟨⟨ Γ ⟩⟩ ⋈ Δ)} →
                    (H : ⟨⟨ Γ ⟩⟩ ⊢H[ Δ ]⦂ X ! (o , i)) →
                    {M : (⟨⟨ Γ ⟩⟩ ⋈ Δ) ⊢M⦂ X ! (hole-ty-hₒ H , hole-ty-hᵢ H)} →
                    y ⧗ M → 
                    -----------------------------------------------------------
                    RunResult⟨ Γ ∣ H [ M ]h ⟩

await-h-runresult [-] p =
  awaiting p
await-h-runresult (promise op ∣ q ↦ N `in H) p =
  promise (await-h-runresult H p)


-- COMPUTATION RESULT CAN BE TURNED INTO A HOISTING CONTEXT

{- LEMMA 4.3 -}

result-to-hoist : {Γ : Ctx}
                  {X : VType}
                  {o : O}
                  {i : I} → 
                  {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ X ! (o , i)} →
                  Result⟨ Γ ∣ M ⟩ →
                  ------------------------------------------------------------------
                  Σ[ Δ ∈ BCtx ] Σ[ H ∈ ⟨⟨ Γ ⟩⟩ ⊢H[ Δ ]⦂ X ! (o , i) ]
                    ((Σ[ V ∈ ⟨⟨ Γ ⟩⟩ ⋈ Δ ⊢V⦂ X ] (M ≡ H [ return V ]h))
                      ⊎
                      (Σ[ op ∈ Σₛ ] Σ[ p ∈ op ∈ₒ hole-ty-hₒ H ]
                        Σ[ V ∈ ⟨⟨ Γ ⟩⟩ ⋈ Δ ⊢V⦂ ``(payload op) ]
                        Σ[ N ∈ ⟨⟨ Γ ⟩⟩ ⋈ Δ ⊢M⦂ X ! (hole-ty-hₒ H , hole-ty-hᵢ H) ]
                        (M ≡ H [ ↑ op p V N ]h))
                      ⊎
                      Σ[ Y ∈ VType ] Σ[ y ∈ ⟨ Y ⟩ ∈ ⟨⟨ Γ ⟩⟩ ⋈ Δ ]
                        Σ[ N ∈ ⟨⟨ Γ ⟩⟩ ⋈ Δ ⊢M⦂ (X ! (hole-ty-hₒ H , hole-ty-hᵢ H)) ]
                        Σ[ p ∈ y ⧗ N ] (M ≡ H [ N ]h))

result-to-hoist (return {X} {o} {i} V) =
   [] , [-] , inj₁ (V , refl) 
result-to-hoist (signal {_} {o} {i} {op} {p} {V} {N} R) =
  [] , [-] , inj₂ (inj₁ (op , p , V , N , refl))
result-to-hoist (promise {Y} {_} {_} {o'} {_} {i'} {op} {p} {N} R) with result-to-hoist R
... | Δ , H , inj₁ (V , q) =
  Y ∷∷ Δ , (promise op ∣ p ↦ N `in H) ,
    inj₁ (V , cong (λ N' → promise op ∣ p ↦ N `in N') q)
... | Δ , H , inj₂ (inj₁ (op' , q , V , N'' , r)) =
  Y ∷∷ Δ , (promise op ∣ p ↦ N `in H) ,
    inj₂ (inj₁ (op' , q , V , N'' , cong (λ N' → promise op ∣ p ↦ N `in N') r))
... | Δ , H , inj₂ (inj₂ (Z , y , N'' , q , r)) =
  Y ∷∷ Δ , (promise op ∣ p ↦ N `in H) ,
    inj₂ (inj₂ (Z , y , N'' , q , cong (λ N' → promise op ∣ p ↦ N `in N') r))
result-to-hoist (awaiting {_} {Y} {y} {N} p) =
  [] , [-] , inj₂ (inj₂ (Y , y , N , p , refl))


-- PROGRESS THEOREM FOR PROCESSES

{- THEOREM 4.4 -}

proc-progress : {o : O} {PP : PType o} →
                (P : [] ⊢P⦂ PP) →
                -------------------------------------------------------------------------------
                (Σ[ o' ∈ O ] Σ[ QQ ∈ PType o' ] Σ[ r ∈ PP ⇝ QQ ] Σ[ Q ∈ [] ⊢P⦂ QQ ] (P [ r ]↝ Q)
                 ⊎
                 Result⟨ P ⟩)

proc-progress {o'} (run {X} {o} {i} M) with progress M
... | inj₁ (N , r) =
  inj₁ (_ , _ , _ , _ , run r)
... | inj₂ R with result-to-hoist R
... | Δ , H , inj₁ (V , p) =
  inj₂ (proc (run (subst (λ M → RunResult⟨ [] ∣ M ⟩) (sym p) (return-h-runresult V H))))
... | Δ , H , inj₂ (inj₁ (op , p , V , N , q)) =
  inj₁ (_ , _ , id ,
        ↑ op (hole-ty-h-⊑ₒ H op p) (strengthen-val {Δ = Δ} V) (run (H [ N ]h)) ,
        subst (λ M → run M [ id ]↝ _) (sym q) (↑ {o' = o'} {i' = i} H p V N))
... | Δ , H , inj₂ (inj₂ (Y , y , N , p , q)) =
  inj₂ (proc (run (subst (λ M → RunResult⟨ [] ∣ M ⟩) (sym q) (await-h-runresult H p))))
proc-progress (P ∥ Q) with proc-progress P
proc-progress (P ∥ Q) | inj₁ (o' , PP' , r , P' , r') =
  inj₁ (_ , _ , _ , _ , context {F = [-] ∥ₗ Q} r')
proc-progress (P ∥ Q) | inj₂ R with proc-progress Q
proc-progress (P ∥ Q) | inj₂ R | inj₁ (o' , QQ' , r , Q' , r') =
  inj₁ (_ , _ , _ , _ , context {F = P ∥ᵣ [-]} r')
proc-progress (P ∥ Q) | inj₂ (proc R) | inj₂ (proc R') =
  inj₂ (proc (par R R'))
proc-progress (P ∥ .(↑ _ _ _ _)) | inj₂ (proc R) | inj₂ (signal {_} {_} {_} {p} {V} {Q} R') =
  inj₁ (_ , _ , _ , _ , ↑-∥ᵣ p V P Q)
proc-progress (.(↑ _ _ _ _) ∥ Q) | inj₂ (signal {_} {_} {_} {p} {V} {P} R) | inj₂ R' =
  inj₁ (_ , _ , _ , _ , ↑-∥ₗ p V P Q)
proc-progress (↑ op p V P) with proc-progress P
proc-progress (↑ op p V P) | inj₁ (o' , PP' , r , P' , r') =
  inj₁ (_ , _ , _ , _ , context {F = ↑ op p V [-]} r')
proc-progress (↑ op p V P) | inj₂ R =
  inj₂ (signal R)
proc-progress (↓ op V P) with proc-progress P
proc-progress (↓ op V P) | inj₁ (o' , OO' , r , P' , r') =
  inj₁ (_ , _ , _ , _ , context {F = ↓ op V [-]} r')
proc-progress (↓ op V .(run _)) | inj₂ (proc (run {_} {_} {_} {M} R)) =
  inj₁ (_ , _ , _ , _ , ↓-run V M)
proc-progress (↓ op V .(_ ∥ _)) | inj₂ (proc (par {_} {_} {_} {_} {P} {Q} R R')) =
  inj₁ (_ , _ , _ , _ , ↓-∥ V P Q)
proc-progress (↓ op V .(↑ _ _ _ _)) | inj₂ (signal {_} {_} {_} {p} {W} {Q} R) =
  inj₁ (_ , _ , _ , _ , ↓-↑ p V W Q)

