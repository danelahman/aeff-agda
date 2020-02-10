open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality)
open import Relation.Nullary
open import Relation.Nullary.Negation

open import EffectAnnotations

module Types where

-- BASE AND GROUND TYPES

postulate BType : Set -- set of base types

postulate dec-bty : (B B' : BType) → Dec (B ≡ B')

GType = BType


-- VALUE AND COMPUTATION TYPES

mutual

  data VType : Set where
    ``  : GType → VType
    _⇒_ : VType → CType → VType
    ⟨_⟩ : VType → VType

  data CType : Set where
    _!_ : VType → O × I → CType

infix 30 _⇒_
infix 30 _!_


-- DECIDABLE EQUALITY OF VALUE AND COMPUTATION TYPES

mutual

  dec-vty : (X Y : VType) → Dec (X ≡ Y)
  dec-vty (`` A) (`` B) with dec-bty A B
  ... | yes refl =
    yes refl
  ... | no ¬p =
    no (λ q → contradiction (inj-`` q) ¬p)

    where
      inj-`` : {A B : BType} → `` A ≡ `` B → A ≡ B
      inj-`` refl = refl

  dec-vty (`` A) (X ⇒ Y) =
    no (λ ())
  dec-vty (`` A) ⟨ Y ⟩ =
    no (λ ())
  dec-vty (X ⇒ C) (`` A) =
    no (λ ())
  dec-vty (X ⇒ C) (Y ⇒ D) with dec-vty X Y | dec-cty C D
  ... | yes refl | yes refl =
    yes refl
  ... | yes refl | no ¬q =
    no (λ r → contradiction (inj-fun₂ r) ¬q)

    where
      inj-fun₂ : {X Y : VType} {C D : CType} → X ⇒ C ≡ Y ⇒ D → C ≡ D
      inj-fun₂ refl = refl

  ... | no ¬p | _ =
    no (λ q → contradiction (inj-fun₁ q) ¬p)

    where
      inj-fun₁ : {X Y : VType} {C D : CType} → X ⇒ C ≡ Y ⇒ D → X ≡ Y
      inj-fun₁ refl = refl

  dec-vty (X ⇒ C) ⟨ Z ⟩ =
    no (λ ())
  dec-vty ⟨ X ⟩ (`` A) =
    no (λ ())
  dec-vty ⟨ X ⟩ (Y ⇒ C) =
    no (λ ())
  dec-vty ⟨ X ⟩ ⟨ Y ⟩ with dec-vty X Y
  ... | yes refl =
    yes refl
  ... | no ¬p =
    no (λ q → contradiction (inj-promise q) ¬p)

    where
      inj-promise : {X Y : VType} → ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y
      inj-promise refl = refl

  dec-cty : (C D : CType) → Dec (C ≡ D)
  dec-cty (X ! (o , i)) (Y ! (o' , i')) with dec-vty X Y | dec-effₒ o o' | dec-effᵢ i i'
  ... | yes refl | yes refl | yes refl =
    yes refl
  ... | yes refl | no ¬q | _ =
    no (λ r → contradiction (inj-cty₂ r) ¬q)

    where
      inj-cty₂ : {X Y : VType} {o o' : O} {i i' : I} → X ! (o , i) ≡ Y ! (o' , i') → o ≡ o'
      inj-cty₂ refl = refl

  ... | yes refl | _ | no ¬q =
    no (λ r → contradiction (inj-cty₃ r) ¬q)

    where
      inj-cty₃ : {X Y : VType} {o o' : O} {i i' : I} → X ! (o , i) ≡ Y ! (o' , i') → i ≡ i'
      inj-cty₃ refl = refl

  ... | no ¬p | _ | _ =
    no (λ q → contradiction (inj-cty₁ q) ¬p)

    where
      inj-cty₁ : {X Y : VType} {o o' : O} {i i' : I} → X ! (o , i) ≡ Y ! (o' , i') → X ≡ Y
      inj-cty₁ refl = refl
