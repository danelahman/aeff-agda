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


-- HOISTING A RETURN VALUE IS A RUN RESULT

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


-- HOISTING AN AWAITING COMPUTATION IS A RUN RESULTS

await-runresult : {Γ : Ctx}
                  {Δ : BCtx}
                  {X Y : VType}
                  {o : O}
                  {i : I} →
                  (y : ⟨ Y ⟩ ∈ (⟨⟨ Γ ⟩⟩ ⋈ Δ)) →
                  (H : ⟨⟨ Γ ⟩⟩ ⊢H[ Δ ]⦂ X ! (o , i)) →
                  (M : (⟨⟨ Γ ⟩⟩ ⋈ Δ) ⊢M⦂ X ! (hole-ty-hₒ H , hole-ty-hᵢ H)) →
                  y ◄ M → 
                  -----------------------------------------------------
                  RunResult⟨ Γ ∣ H [ M ]ₕ ⟩

await-runresult y [-] M p =
  awaiting p
await-runresult y (promise op ∣ q ↦ N `in H) M p =
  promise (await-runresult y H M p)


-- PROGRESS FOR HOISTING SIGNALS

bctx-to-ctx-wrap : (Γ : Ctx) →
                   (Δ : BCtx) →
                   ------------------------------------
                   append Γ ⟨⟨ bctx-to-ctx Δ ⟩⟩ ≡ Γ ⋈ Δ

bctx-to-ctx-wrap Γ [] =
  refl
bctx-to-ctx-wrap Γ (X ∷∷ Δ) =
  trans (cong (λ Γ'' → append Γ Γ'') (⟨⟨⟩⟩-append ([] ∷ X) (bctx-to-ctx Δ)))
        (trans (append-assoc Γ ([] ∷ ⟨ X ⟩) ⟨⟨ bctx-to-ctx Δ ⟩⟩)
               (bctx-to-ctx-wrap (Γ ∷ ⟨ X ⟩) Δ))


bctx-ctx-ren : (Δ : BCtx) → Ren ⟨⟨ bctx-to-ctx Δ ⟩⟩ ([] ⋈ Δ)
bctx-ctx-ren Δ {X} x =
  subst (λ Γ → X ∈ Γ) (trans append-lunit (bctx-to-ctx-wrap [] Δ)) x


bctx-ctx-ren-var : (Δ : BCtx) → (X : VType) → Ren (⟨⟨ bctx-to-ctx Δ ⟩⟩ ∷ ⟨ X ⟩) ⟨⟨ bctx-to-ctx (Δ ++ X ∷∷ []) ⟩⟩
bctx-ctx-ren-var Δ X {Y} x =
  subst (λ Γ → Y ∈ Γ) (cong (λ Γ → ⟨⟨ Γ ⟩⟩) (sym (bctx-to-ctx-append {Δ} {⟦ X ⟧}))) x


run-progress : {Δ : BCtx}
               {X : VType}
               {o : O}
               {i : I}
               (H : [] ⊢H[ Δ ]⦂ X ! (o , i)) → 
               {M : ⟨⟨ bctx-to-ctx Δ ⟩⟩ ⊢M⦂ X ! (hole-ty-hₒ H , hole-ty-hᵢ H)} →
               Result⟨ bctx-to-ctx Δ ∣ M ⟩ →
               -----------------------------------------------------------------
               Σ[ o' ∈ O ]
                 Σ[ QQ ∈ PType o' ]
                 Σ[ r ∈ X ‼ o , i ⇝ QQ ]
                 Σ[ Q ∈ [] ⊢P⦂ QQ ]
                 (run (H [ M-rename (bctx-ctx-ren Δ) M ]ₕ) [ r ]↝ Q)
               ⊎
               Result⟨ run (H [ M-rename (bctx-ctx-ren Δ) M ]ₕ) ⟩

run-progress {Δ} H (return {X} V) =
  inj₂ (proc (run (hoist-runresult (V-rename (bctx-ctx-ren Δ) V) H)))
run-progress {Δ} H (signal {X} {o} {i} {op} {p} {V} {M'} R) =
  inj₁ (_ , _ , id , _ , ↑ {o' = o} {i' = i} H p (V-rename (bctx-ctx-ren Δ) V) (M-rename (bctx-ctx-ren Δ) M'))
run-progress {Δ} {X''} {o''} {i''} H (promise {X} {Y} {o} {o'} {i} {i'} {op} {p} {M} {N} R)
  with run-progress (H [ promise op ∣ p ↦ (M-rename (wk₂ (bctx-ctx-ren Δ)) M) `in [-] ]ₕₕ)
                    {M-rename (bctx-ctx-ren-var Δ X) {!!}}
                    {!!}
... | q =
  {!!}
run-progress {Δ} H (awaiting {C} {Y} {y} {M} p) =
  inj₂ (proc (run (await-runresult (bctx-ctx-ren Δ y) H (M-rename (bctx-ctx-ren Δ) M) (◄-ren p))))






-- PROGRESS THEOREM FOR PROCESSES

cong₂ᵢ : {A B C : Set} → (f : {a : A} → B → C) → {x y : A} → {u v : B} → x ≡ y → u ≡ v → f {x} u ≡ f {y} v
cong₂ᵢ f refl refl = refl


proc-progress : {o : O} {PP : PType o} →
                (P : [] ⊢P⦂ PP) →
                -------------------------------------------------------------------------------
                (Σ[ o' ∈ O ] Σ[ QQ ∈ PType o' ] Σ[ r ∈ PP ⇝ QQ ] Σ[ Q ∈ [] ⊢P⦂ QQ ] (P [ r ]↝ Q)
                 ⊎
                 Result⟨ P ⟩)

proc-progress (run {X} {o} {i} M) with progress M
... | inj₁ (N , r) =
  inj₁ (_ , _ , _ , _ , run r)
... | inj₂ R =
  subst (λ M → (Σ[ o' ∈ O ]
                  Σ[ QQ ∈ PType o' ]
                  Σ[ r ∈ (X ‼ o , i) ⇝ QQ ]
                  Σ[ Q ∈ [] ⊢P⦂ QQ ]
                  ((run M) [ r ]↝ Q)
                ⊎
                Result⟨ run M ⟩))
        (trans (cong (λ (r : Ren [] []) → M-rename r M)
                     (ifun-ext λ {X} → fun-ext (λ x → sym (ren-[]-id (bctx-ctx-ren []) x))))
               (M-rename-id-lem M))
        (run-progress [-] R)
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