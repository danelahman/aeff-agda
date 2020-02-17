open import Data.Empty
open import Data.List renaming (_∷_ to _∷∷_ ; [_] to ⟦_⟧)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Calculus
open import EffectAnnotations
open import Preservation
open import ProcessCalculus
open import ProcessPreservation
open import ProcessTypes
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
             --------------------------------------
             RunResult⟨ Γ ∣ return {o = o} {i = i} V ⟩

  promise  : {X Y : VType}
             {o o' : O}
             {i i' : I}
             {op : Σₙ}
             {p : lkpᵢ op i ≡ just (o' , i')}
             {M : ⟨⟨ Γ ⟩⟩ ∷ ``(arₙ op) ⊢M⦂ X ! (o' , i')}
             {N : ⟨⟨ Γ ⟩⟩ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)} →
             RunResult⟨ Γ ∷ X ∣ N ⟩ →
             -------------------------------------------
             RunResult⟨ Γ ∣ promise op ∣ p ↦ M `in N ⟩

  awaiting : {C : CType}
             {Y : VType}
             {y : ⟨ Y ⟩ ∈ ⟨⟨ Γ ⟩⟩}
             {M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C} → 
             y ◄ M →
             --------------------------------
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
           --------------------------
           ParResult⟨ P ∥ Q ⟩


data Result⟨_⟩ : {o : O} {PP : PType o} → [] ⊢P⦂ PP → Set where

  proc   : {o : O}
           {PP : PType o}
           {P : [] ⊢P⦂ PP} →
           ParResult⟨ P ⟩ →
           --------------------------
           Result⟨ P ⟩

  signal : {o : O}
           {PP : PType o}
           {op : Σₙ}
           {p : op ∈ₒ o}
           {V : [] ⊢V⦂ ``(arₙ op)}
           {P : [] ⊢P⦂ PP} →
           Result⟨ P ⟩ →
           -----------------------
           Result⟨ ↑ op p V P ⟩



{-
-- PROGRESS FOR HOISTING SIGNALS

bctx-to-ctx-wrap : (Γ : Ctx) →
                   (Δ : BCtx) →
                   ------------------------------------
                   append Γ ⟨⟨ bctx-to-ctx Δ ⟩⟩ ≡ Γ ⋈ Δ

bctx-to-ctx-wrap Γ [] =
  refl
bctx-to-ctx-wrap Γ (X ∷∷ Δ) =
  trans (cong (λ Γ'' → append Γ Γ'') (⟨⟨⟩⟩-append ([] ∷ X) (bctx-to-ctx Δ)))
        (trans (append-trans Γ ([] ∷ ⟨ X ⟩) ⟨⟨ bctx-to-ctx Δ ⟩⟩)
               (bctx-to-ctx-wrap (Γ ∷ ⟨ X ⟩) Δ))


bctx-ctx-comp : {Γ : Ctx}
                {Δ : BCtx}
                {C : CType} → 
                (append Γ ⟨⟨ bctx-to-ctx Δ ⟩⟩) ⊢M⦂ C →
                --------------------------------------
                Γ ⋈ Δ ⊢M⦂ C

bctx-ctx-comp {Γ} {Δ} {C} M =
  subst (λ Γ → Γ ⊢M⦂ C)
        (bctx-to-ctx-wrap Γ Δ)
        M


bctx-ctx-comp-[] : {Δ : BCtx}
                   {C : CType} → 
                   ⟨⟨ bctx-to-ctx Δ ⟩⟩ ⊢M⦂ C →
                   ---------------------------
                   [] ⋈ Δ ⊢M⦂ C

bctx-ctx-comp-[] {Δ} {C} M =
  bctx-ctx-comp {Γ = []} {Δ = Δ} (subst (λ Γ → Γ ⊢M⦂ C) append-lunit M)


bctx-ctx-comp-coherence : {X : VType}
                          {o : O}
                          {i : I}
                          {Δ : BCtx}
                          (V : ⟨⟨ bctx-to-ctx Δ ⟩⟩ ⊢V⦂ X) →
                          ---------------------------------
                          bctx-ctx-comp-[] {Δ = Δ} (return {o = o} {i = i} V)
                          ≡
                          return (subst (λ Γ → Γ ⊢V⦂ X) (trans append-lunit (bctx-to-ctx-wrap [] Δ)) V)

bctx-ctx-comp-coherence {X} {o} {i} {Δ} V with bctx-to-ctx-wrap [] Δ
... | p = {!!}


hoist-runresult : {Γ : Ctx}
                  {Δ : BCtx}
                  {X : VType}
                  {o : O}
                  {i : I}
                  (V : (⟨⟨ Γ ⟩⟩ ⋈ Δ) ⊢V⦂ X) →
                  (H : ⟨⟨ Γ ⟩⟩ ⊢H[ Δ ]⦂ X ! (o , i)) →
                  ------------------------------------
                  RunResult⟨ Γ ∣ H [ return V ]ₕ ⟩

hoist-runresult V [-] =
  return V
hoist-runresult V (promise op ∣ p ↦ M `in H) =
  promise (hoist-runresult V H)





bctx-ctx-sub : (Δ : BCtx) → Sub ⟨⟨ bctx-to-ctx Δ ⟩⟩ ([] ⋈ Δ)
bctx-ctx-sub Δ =
  subst (λ Γ → Sub ⟨⟨ bctx-to-ctx Δ ⟩⟩ Γ) (trans append-lunit (bctx-to-ctx-wrap [] Δ)) id-subst


run-progress : {Δ : BCtx}
               {X : VType}
               {o : O}
               {i : I}
               (H : [] ⊢H[ Δ ]⦂ X ! (o , i)) → 
               {M : ⟨⟨ bctx-to-ctx Δ ⟩⟩ ⊢M⦂ X ! (hole-ty-hₒ H , hole-ty-hᵢ H)} →
               Result⟨ bctx-to-ctx Δ ∣ M ⟩ →
               ---------------------------------------------------------------------------------------------------------------------------
               Σ[ o' ∈ O ] Σ[ QQ ∈ PType o' ] Σ[ r ∈ X ‼ o , i ⇝ QQ ] Σ[ Q ∈ [] ⊢P⦂ QQ ] (run (H [ M [ bctx-ctx-sub Δ ]m ]ₕ) [ r ]↝ Q)
               ⊎
               Result⟨ run (H [ M [ bctx-ctx-sub Δ ]m ]ₕ) ⟩

run-progress {Δ} H (return {X} V) =
  inj₂ (run {!!})
run-progress H (signal {X} {o} {i} {op} {p} {V} {M'} R) =
  inj₁ ({!!} , {!!} , {!!} , {!!} , {!!})
run-progress H (promise R) =
  {!!}
run-progress H (awaiting p) =
  inj₂ (run {!!})


-- [ bctx-ctx-comp-[] {Δ = Δ} M ]








-- PROGRESS THEOREM FOR PROCESSES

proc-progress : {o : O} {PP : PType o} →
                (P : [] ⊢P⦂ PP) →
                -------------------------------
                (Σ[ o' ∈ O ] Σ[ QQ ∈ PType o' ] Σ[ r ∈ PP ⇝ QQ ] Σ[ Q ∈ [] ⊢P⦂ QQ ] (P [ r ]↝ Q)
                 ⊎
                 Result⟨ P ⟩)

proc-progress (run M) with progress M
proc-progress (run M) | inj₁ (N , p) =
  inj₁ (_ , _ , id , run N , run p)
... | inj₂ (return V) =
  inj₂ (run (return V))
... | inj₂ (signal {X} {o} {i} {op} {p} {V} {M'} R) =
  inj₁ (_ , _ , id , ↑ op p (strengthen-val {Δ = []} V) (run ([-] [ M' ]ₕ)) , ↑ {o' = o} {i' = i} [-] p V M')
... | inj₂ (promise R) =
  {!!}
proc-progress (P ∥ Q) = {!!}
proc-progress (↑ op p V P) = {!!}
proc-progress (↓ op V P) = {!!}




-}



{-
  

progress : {Γ : Ctx} {C : CType} →
           (M : ⟨⟨ Γ ⟩⟩ ⊢M⦂ C) →
           -------------------------------
           (Σ[ N ∈ ⟨⟨ Γ ⟩⟩ ⊢M⦂ C ] (M ↝ N)
            ⊎
            Result⟨ Γ ∣ M ⟩)

progress (return V) =
  inj₂ (return V)
progress (let= M `in N) with progress M
... | inj₁ (M' , r) =
  inj₁ (let= M' `in N , context (let= [-] `in N) r)
... | inj₂ (return V) =
  inj₁ (N [ `_ [ V ]s ]m , let-return V N)
... | inj₂ (signal {X} {o} {i} {op} {p} {V} {M'} r) =
  inj₁ (↑ op p V (let= M' `in N) , let-↑ p V M' N)
... | inj₂ (promise {X} {Y} {o} {o'} {i} {i'} {op} {p} {M'} {M''} r) =
  inj₁ ((promise op ∣ p ↦ M' `in (let= M'' `in M-rename (comp-ren exchange wk₁) N)) , let-promise p M' M'' N)
... | inj₂ (awaiting r) =
  inj₂ (awaiting (let-in r))
progress ((` x) · W) with ⇒-not-in-ctx x
... | ()
progress (ƛ M · W) =
  inj₁ (M [ id-subst [ W ]s ]m , apply M W)
progress (↑ op p V M) with progress M
... | inj₁ (N , r) =
  inj₁ (↑ op p V N , (context (↑ op p V [-]) r))
... | inj₂ r =
  inj₂ (signal r)
progress (↓ op V M) with progress M
progress (↓ op V M) | inj₁ (N , r) =
  inj₁ (↓ op V N , context (↓ op V [-]) r)
... | inj₂ (return W) =
  inj₁ (return W , ↓-return V W)
... | inj₂ (signal {X} {o} {i} {op'} {p} {W'} {M'} q) =
  inj₁ (↑ op' (↓ₑ-⊑ₒ op' p) W' (↓ op V M') , ↓-↑ p V W' M')
... | inj₂ (promise {X} {Y} {o} {o'} {i} {i'} {op'} {p} {M'} {M''} q) with decₙ op op'
... | yes refl =
  inj₁ (let= (subsume (↓ₑ-⊑ₒ-o' {o} p) (↓ₑ-⊑ₒ-i' {o} p) (M' [ id-subst [ V ]s ]m)) `in
             ↓ op (V-rename wk₁ V) ((M-rename (comp-ren exchange wk₁) M'') [ id-subst [ ⟨ ` Hd ⟩ ]s ]m) ,
        ↓-promise-op p V M' M'')
... | no ¬r =
  inj₁ (promise_∣_↦_`in_ {o' = proj₁ (lkpᵢ-↓ₑ-neq {o = o} {i = i} ¬r p)}
                         {i' = proj₁ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} ¬r p))}
                         op'
                         (proj₁ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} ¬r p))))
                         (subsume (proj₁ (proj₂ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} ¬r p)))))
                                  (proj₂ (proj₂ (proj₂ (proj₂ (lkpᵢ-↓ₑ-neq {o = o} {i = i} ¬r p)))))
                                  M')
                         (↓ op (V-rename wk₁ V) M'') ,
        ↓-promise-op' ¬r p V M' M'')
progress (↓ op V M) | inj₂ (awaiting r) =
  inj₂ (awaiting (interrupt r))
progress (promise op ∣ p ↦ M `in N) with progress N
... | inj₁ (N' , r) =
  inj₁ (promise op ∣ p ↦ M `in N' , context (promise op ∣ p ↦ M `in [-]) r)
... | inj₂ r =
  inj₂ (promise r)
progress (await ` x until M) =
  inj₂ (awaiting await)
progress (await ⟨ V ⟩ until M) =
  inj₁ (M [ `_ [ V ]s ]m , await-promise V M)
progress (subsume p q M) with progress M
... | inj₁ (N , r) =
  inj₁ (subsume p q N , context (subsume p q [-]) r)
... | inj₂ (return V) =
  inj₁ (return V , subsume-return V)
... | inj₂ (signal {X} {o} {i} {op} {r} {V} {M'} s) =
  inj₁ (↑ op (p op r) V (subsume p q M') , subsume-↑ r V M')
... | inj₂ (promise {X} {Y} {o} {o'} {i} {i'} {op} {r} {M'} {M''} s) =
  inj₁
    ((promise op ∣ lkpᵢ-next-eq q r ↦
      subsume (lkpᵢ-next-⊑ₒ q r) (lkpᵢ-next-⊑ᵢ q r) M' `in
      subsume p q M'')
     , subsume-promise r M' M'')
... | inj₂ (awaiting r) =
  inj₂ (awaiting (subsume r))


-- PROGRESS THEOREM FOR CLOSED COMPUTATIONS

closed-progress : {C : CType} →
                  (M : [] ⊢M⦂ C) →
                  --------------------------
                  (Σ[ N ∈ [] ⊢M⦂ C ] (M ↝ N)
                   ⊎
                   Result⟨ [] ∣ M ⟩)

closed-progress M =
  progress M

-}
