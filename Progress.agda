open import Data.Empty
open import Data.List hiding ([_]) renaming (_∷_ to _::_)
open import Data.Maybe
open import Data.Product
open import Data.Sum

open import Calculus
open import EffectAnnotations
open import Preservation
open import Renamings
open import Substitutions
open import Types

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

module Progress where


-- COMPUTATIONS THAT ARE STUCK ON WAITING FOR A PARTICULAR PROMISE
    
data _◄_ {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) : {C : CType} → Γ ⊢M⦂ C → Set where

  await     : {C : CType}
              {M : Γ ∷ X ⊢M⦂ C} →
              -------------------------
              x ◄ (await (` x) until M)

  let-in    : {X Y : VType}
              {o : O}
              {i : I}
              {M : Γ ⊢M⦂ X ! (o , i)}
              {N : Γ ∷ X ⊢M⦂ Y ! (o , i)} →
              x ◄ M →
              -----------------------------
              x ◄ (let= M `in N)

  interrupt : {X : VType}
              {o : O}
              {i : I}
              {op : Σᵢ}
              {V : Γ ⊢V⦂ ``(arᵢ op)}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ◄ M →
              -------------------------
              x ◄ (↓ op V M)

  subsume   : {X : VType}
              {o o' : O}
              {i i' : I}
              {p : o ⊑ₒ o'}
              {q : i ⊑ᵢ i'}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ◄ M →
              -------------------------
              x ◄ (subsume p q M)

data _◅_ {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) : {C : CType} → Γ ⊢M⦂ C → Set where

  ◅◄        : {C : CType}
              {M : Γ ⊢M⦂ C} →
              x ◄ M →
              ---------------
              x ◅ M

  signal    : {X : VType}
              {o : O}
              {i : I}
              {op : Σₒ}
              {p : op ∈ₒ o}
              {V : Γ ⊢V⦂ ``(arₒ op)}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ◅ M →
              -------------------------
              x ◅ (↑ op p V M)

  promise   : {X Y : VType}
              {o o' : O}
              {i i' : I} 
              {op : Σᵢ}
              {p : lkpᵢ op i ≡ just (o' , i')}
              {M : Γ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i')}
              {N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)} →
              Tl x ◅ N →
              ----------------------------------
              x ◅ (promise op ∣ p ↦ M `in N)

  subsume   : {X : VType}
              {o o' : O}
              {i i' : I}
              {p : o ⊑ₒ o'}
              {q : i ⊑ᵢ i'}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ◅ M →
              -------------------------
              x ◅ (subsume p q M)


-- DECIDING IF A COMPUTATION IS STUCK ON WAITING FOR A PARTICULAR PROMISE

if-¬◄-then-¬◅ : {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) → {C : CType} → (M : Γ ⊢M⦂ C) → ¬(x ◄ M) → ¬(x ◅ M)
if-¬◄-then-¬◅ = {!!}

dec◄ : {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) → {C : CType} → (M : Γ ⊢M⦂ C) → Dec (x ◄ M)
dec◄ x (return V) =
  no (λ ())
dec◄ {Γ} {X} x (let= M `in N) with dec◄ x M
... | yes p =
  yes (let-in p)
... | no ¬p =
  no (λ q → contradiction (inj-let q) ¬p)

  where
    inj-let : {Y Z : VType} {o : O} {i : I} {M : Γ ⊢M⦂ Y ! (o , i)} {N : Γ ∷ Y ⊢M⦂ Z ! (o , i)} → x ◄ (let= M `in N) → x ◄ M
    inj-let (let-in r) = r

dec◄ x (V · W) =
  no (λ ())
dec◄ x (↑ op p V M) =
  no (λ ())
dec◄ {Γ} {X} x (↓ op V M) with dec◄ x M
... | yes p =
  yes (interrupt p)
... | no ¬p =
  no (λ q → contradiction (inj-interrupt q) ¬p)

  where
    inj-interrupt : {Y : VType} {o : O} {i : I} {op : Σᵢ} {V : Γ ⊢V⦂ ``(arᵢ op)} {M : Γ ⊢M⦂ Y ! (o , i)} → x ◄ ↓ op V M → x ◄ M
    inj-interrupt (interrupt r) = r

dec◄ x (promise op ∣ p ↦ M `in N) =
  no (λ ())
  
dec◄ {Γ} {X} x (await_until_ {Y} (` y) M) with dec-vty X Y
dec◄ {Γ} {.Y} x (await_until_ {Y} (` y) M) | yes refl with dec-var x y
dec◄ {Γ} {.Y} x (await_until_ {Y} (` .x) M) | yes refl | yes refl =
  yes await
dec◄ {Γ} {.Y} x (await_until_ {Y} (` y) M) | yes refl | no ¬p =
  no (λ q → contradiction (inj-await-var q) ¬p)

  where
    inj-await-var : {x y : ⟨ Y ⟩ ∈ Γ} → x ◄ (await (` y) until M) → x ≡ y
    inj-await-var await = refl

dec◄ {Γ} {X} x (await_until_ {Y} (` y) M) | no ¬p =
  no (λ q → contradiction (inj-await-ty q) ¬p)

  where
    inj-await-ty : {X Y : VType} {C : CType} {x : ⟨ X ⟩ ∈ Γ} {y : ⟨ Y ⟩ ∈ Γ} {M : Γ ∷ Y ⊢M⦂ C} → x ◄ (await (` y) until M) → X ≡ Y
    inj-await-ty await = refl
  
dec◄ x (await ⟨ V ⟩ until M) =
  no impossible-await

  where
    impossible-await : ¬ (x ◄ (await ⟨ V ⟩ until M))
    impossible-await ()

dec◄ {Γ} {X} x (subsume p q M) with dec◄ x M
... | yes r =
  yes (subsume r)
... | no ¬r =
  no (λ s → contradiction (inj-subsume s) ¬r)

  where
    inj-subsume : {Y : VType} {o o' : O} {i i' : I} {p : o ⊑ₒ o'} {q : i ⊑ᵢ i'} {M : Γ ⊢M⦂ Y ! (o , i)} → x ◄ subsume p q M → x ◄ M
    inj-subsume (subsume r) = r


dec◅ : {Γ : Ctx} {X : VType} (x : ⟨ X ⟩ ∈ Γ) → {C : CType} → (M : Γ ⊢M⦂ C) → Dec (x ◅ M)
dec◅ x (return V) =
  {!!}
dec◅ x (let= M `in N) =
  {!!}
dec◅ x (V · W) =
  {!!}
dec◅ x (↑ op p V M) =
  {!!}
dec◅ x (↓ op V M) with dec◄ x (↓ op V M)
... | yes p =
  yes (◅◄ p)
... | no ¬p =
  no (λ q → contradiction q (contraposition (λ { (◅◄ r) → r }) ¬p))
dec◅ x (promise op ∣ p ↦ M `in N) with dec◅ (Tl x) N 
... | yes q =
  yes (promise q)
... | no ¬q =
  no (λ { (◅◄ r) → contradiction r (contraposition (λ ()) ¬q) ;
          (promise r) → ¬q r})
dec◅ {Γ} x (await V until M) with dec◄ x (await V until M)
... | yes await =
  yes (◅◄ await)
... | no ¬p =
  no (λ q → contradiction q (contraposition (λ { (◅◄ r) → r }) ¬p))    
dec◅ {Γ} x (subsume p q M) with dec◅ x M
... | yes r =
  yes (subsume r)
... | no ¬r =
  no (λ { (◅◄ t) → contradiction t (contraposition (λ { (subsume s) → s }) (contraposition ◅◄ ¬r)) ;
          (subsume r) → ¬r r })

{-
dec◅ x M with dec◄ x M
dec◅ x .(await ` x until _) | yes await =
  yes (◅◄ await)
dec◅ x .(let= _ `in _) | yes (let-in p) =
  yes (◅◄ (let-in p))
dec◅ {Γ} {X} x {C} .(↓ {o = o} op V M) | yes (interrupt {Y} {o} {i} {op} {V} {M} p) =
  yes (◅◄ (interrupt p))
dec◅ x .(subsume _ _ _) | yes (subsume p) =
  yes (◅◄ (subsume p))
dec◅ {Γ} x (return V) | no ¬p =
  no (λ q → contradiction (inj-return q) ¬p)

  where
    inj-return : {Y : VType} {o : O} {i : I} {V : Γ ⊢V⦂ Y} → x ◅ return {o = o} {i = i} V → x ◄ return {o = o} {i = i} V
    inj-return (◅◄ p) = p

dec◅ x (let= M `in N) | no ¬p =
  {!!}
dec◅ {Γ} x (V · W) | no ¬p =
  no (λ q → contradiction (inj-app q) ¬p)

  where
    inj-app : {Y : VType} {C : CType} {V : Γ ⊢V⦂ Y ⇒ C} {W : Γ ⊢V⦂ Y} → x ◅ (V · W) → x ◄ (V · W)
    inj-app (◅◄ p) = p

dec◅ x (↑ op p V M) | no ¬q =
  {!!}
dec◅ x (↓ op V M) | no ¬p =
  {!!}
dec◅ x (promise op ∣ p ↦ M `in N) | no ¬q =
  {!!}
dec◅ x (await V until M) | no ¬p =
  {!!}
dec◅ {Γ} x (subsume p q M) | no ¬r =
  {!!}

  where
    inj-subsume : {Y : VType} {o o' : O} {i i' : I} {p : o ⊑ₒ o'} {q : i ⊑ᵢ i'} {M : Γ ⊢M⦂ Y ! (o , i)} → x ◅ (subsume p q M) → x ◄ (subsume p q M)
    inj-subsume (◅◄ p) = p
    inj-subsume (subsume p) = {!!}
-}

{-
  interrupt : {X : VType}
              {o : O}
              {i : I}
              {op : Σᵢ}
              {V : Γ ⊢V⦂ ``(arᵢ op)}
              {M : Γ ⊢M⦂ X ! (o , i)} →
              x ◄ M →
              -------------------------
              x ◄ (↓ op V M)
-}


-- WRAPPING PROMISES AROUND A CONTEXT

⟨⟨_⟩⟩ : Ctx → Ctx
⟨⟨ [] ⟩⟩ = []
⟨⟨ Δ ∷ X ⟩⟩ = ⟨⟨ Δ ⟩⟩ ∷ ⟨ X ⟩


-- RESULTS

data Result⟨_∣_⟩ (Δ : Ctx) : {C : CType} → ⟨⟨ Δ ⟩⟩ ⊢M⦂ C → Set where

  return  : {X : VType}
            {o : O}
            {i : I}
            (V : ⟨⟨ Δ ⟩⟩ ⊢V⦂ X) →
            --------------------------------------
            Result⟨ Δ ∣ return {o = o} {i = i} V ⟩

  signal  : {X : VType}
            {o : O}
            {i : I}
            (op : Σₒ) →
            (p : op ∈ₒ o) →
            (V : ⟨⟨ Δ ⟩⟩ ⊢V⦂ ``(arₒ op)) →
            (M : ⟨⟨ Δ ⟩⟩ ⊢M⦂ X ! (o , i)) →
            Result⟨ Δ ∣ M ⟩ →
            -------------------------------
            Result⟨ Δ ∣ ↑ op p V M ⟩

  promise : {X Y : VType}
            {o o' : O}
            {i i' : I}
            (op : Σᵢ) →
            (p : lkpᵢ op i ≡ just (o' , i')) →
            (M : ⟨⟨ Δ ⟩⟩ ∷ ``(arᵢ op) ⊢M⦂ X ! (o' , i')) →
            (N : ⟨⟨ Δ ⟩⟩ ∷ ⟨ X ⟩ ⊢M⦂ Y ! (o , i)) →
            (Result⟨ Δ ∷ X ∣ N ⟩
             ⊎
             (Hd ◅ N)) →
            ----------------------------------------------
            Result⟨ Δ ∣ promise op ∣ p ↦ M `in N ⟩
 


