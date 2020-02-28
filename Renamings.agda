open import AEff
open import EffectAnnotations
open import Types hiding (``)

open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality)
--open ≡-Reasoning

module Renamings where

-- SET OF RENAMINGS BETWEEN CONTEXTS

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : VType} → X ∈ Γ → X ∈ Γ'


-- IDENTITY, COMPOSITION, AND EXCHANGE RENAMINGS

id-ren : {Γ : Ctx} → Ren Γ Γ 
id-ren {X} x = x


comp-ren : {Γ Γ' Γ'' : Ctx} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ'' 
comp-ren f g x = f (g x)


exchange : {Γ : Ctx} {X Y : VType} → Ren (Γ ∷ X ∷ Y) (Γ ∷ Y ∷ X)
exchange Hd = Tl Hd
exchange (Tl Hd) = Hd
exchange (Tl (Tl x)) = Tl (Tl x)


-- WEAKENING OF RENAMINGS

wk₁ : {Γ : Ctx} {X : VType} → Ren Γ (Γ ∷ X)
wk₁ = Tl


wk₂ : {Γ Γ' : Ctx} {X : VType} → Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
wk₂ f Hd = Hd
wk₂ f (Tl v) = Tl (f v)


wk₃ : {Γ : Ctx} {X Y Z : VType} → Ren (Γ ∷ Y ∷ Z) (Γ ∷ X ∷ Y ∷ Z)
wk₃ Hd = Hd
wk₃ (Tl Hd) = Tl Hd
wk₃ (Tl (Tl x)) = Tl (Tl (Tl x))


-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

mutual

  V-rename : {X : VType} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X
  V-rename f (` x) = ` f x
  V-rename f (`` c) = `` c
  V-rename f (ƛ M) = ƛ (M-rename (wk₂ f) M)
  V-rename f ⟨ V ⟩ = ⟨ V-rename f V ⟩

  M-rename : {C : CType} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢M⦂ C → Γ' ⊢M⦂ C
  M-rename f (return V) =
    return (V-rename f V)
  M-rename f (let= M `in N) =
    let= M-rename f M `in M-rename (wk₂ f) N
  M-rename f (letrec M `in N) =
    letrec M-rename (wk₂ (wk₂ f)) M `in M-rename (wk₂ f) N
  M-rename f (V · W) =
    V-rename f V · V-rename f W
  M-rename f (↑ op p V M) =
    ↑ op p (V-rename f V) (M-rename f M)
  M-rename f (↓ op V M) =
    ↓ op (V-rename f V) (M-rename f M)
  M-rename f (promise op ∣ p ↦ M `in N) =
    promise op ∣ p ↦ M-rename (wk₂ f) M `in M-rename (wk₂ f) N
  M-rename f (await V until M) =
    await (V-rename f V) until (M-rename (wk₂ f) M)
  M-rename f (coerce p q M) =
    coerce p q (M-rename f M)


-- ACTION OF RENAMING ON WELL-TYPED PROCESSES

P-rename : {o : O} {PP : PType o} {Γ Γ' : Ctx} → Ren Γ Γ' → Γ ⊢P⦂ PP → Γ' ⊢P⦂ PP
P-rename f (run M) =
  run (M-rename f M)
P-rename f (P ∥ Q) =
  P-rename f P ∥ P-rename f Q
P-rename f (↑ op p V P) =
  ↑ op p (V-rename f V) (P-rename f P)
P-rename f (↓ op V P) =
  ↓ op (V-rename f V) (P-rename f P)
