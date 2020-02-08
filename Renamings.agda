open import Calculus
open import Operations
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])

module Renamings where

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : VType} → X ∈ Γ → X ∈ Γ'

id-ren : {Γ : Ctx} → Ren Γ Γ 
id-ren x = x

comp-ren : {Γ Γ' Γ'' : Ctx} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ'' 
comp-ren f g x = f (g x)

exchange : {Γ : Ctx} {X Y : VType} → Ren (Γ ∷ X ∷ Y) (Γ ∷ Y ∷ X)
exchange Hd = Tl Hd
exchange (Tl Hd) = Hd
exchange (Tl (Tl x)) = Tl (Tl x)

wk₁ : {Γ : Ctx} {X : VType} → Ren Γ (Γ ∷ X)
wk₁ = Tl

wk₂ : {Γ Γ' : Ctx} {X : VType} → Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
wk₂ f Hd = Hd
wk₂ f (Tl v) = Tl (f v)

wk₂-id-lem : {Γ : Ctx}
             {X Y : VType} →
             (x : Y ∈ (Γ ∷ X)) →
             ---------------------------
             (wk₂ id-ren x) ≡ (id-ren x)
wk₂-id-lem Hd = refl
wk₂-id-lem (Tl x) = refl

wk₂-comp-lem : {Γ Γ' Γ'' : Ctx}
               {X Y : VType}
               {g : Ren Γ' Γ''}
               {f : Ren Γ Γ'} →
               (x : Y ∈ (Γ ∷ X)) →
               ------------------------------------------------
               comp-ren (wk₂ g) (wk₂ f) x ≡ wk₂ (comp-ren g f) x
wk₂-comp-lem Hd = refl
wk₂-comp-lem (Tl x) = refl
