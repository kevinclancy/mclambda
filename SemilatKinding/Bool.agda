module SemilatKinding.Bool where

open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.Closure.ReflexiveTransitive
open import UnitPoset
open import Data.List
open import Data.List.Any
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Bool

open import Function using (_$_)

open import SemilatKinding.Core
open import Relation.Binary
open import RelationalStructures
open import Level 
open import Syntax
open import Kinding
open import Util
open import SemDeltaPoset
open import FreeForgetfulAdjunction
open import BoolPoset
open import FinPoset
open import SemPoset

lowerˡ : ∀ (a b : Bool) → a B≤ a B∨ b
lowerˡ false false = ε
lowerˡ false true = (here $ PE.refl , PE.refl) ◅ ε
lowerˡ true false = ε
lowerˡ true true = ε

lowerʳ : ∀ (a b : Bool) → b B≤ a B∨ b
lowerʳ false false = ε
lowerʳ false true = ε
lowerʳ true false = (here $ PE.refl , PE.refl) ◅ ε
lowerʳ true true = ε

least : ∀ (a b : Bool) → (z : Bool) → (a B≤ z) → (b B≤ z) → (a B∨ b B≤ z) 
least false false false a≤z b≤z = ε
least false false true a≤z b≤z = (here $ PE.refl , PE.refl) ◅ ε
least false true false a≤z (here () ◅ _)
least false true false a≤z (there () ◅ _)
least false true true a≤z b≤z = ε
least true false false (here () ◅ _) b≤z
least true false false (there () ◅ _) b≤z
least true false true a≤z b≤z = ε
least true true false (here () ◅ _) b≤z
least true true false (there () ◅ _) b≤z
least true true true a≤z b≤z = ε

minimum : Minimum _B≤_ false
minimum false = ε
minimum true = (here $ PE.refl , PE.refl) ◅ ε

S : BoundedJoinSemilattice l0 l0 l0
S = record 
  { Carrier = Bool
  ; _≈_ = _≡_
  ; _≤_ = _B≤_
  ; _∨_ = _B∨_ 
  ; ⊥ = false
  ; isBoundedJoinSemilattice = record
    { isJoinSemilattice = record
      { isPartialOrder = B≤-isPartialOrder
      ; supremum =  λ x → λ y → lowerˡ x y , lowerʳ x y , least x y
      }
    ; minimum = minimum 
    } 
  }

P : DeltaPoset {l0} {l0} {l0} {l0}
P = ⟦ UnitDelta ⁑⟧ 

|i| : (DeltaPoset.Carrier P) → (DeltaPoset.Carrier ⟦ UnitDelta ⁑⟧)
|i| tt = tt

|i|-monotone : Monotone (DeltaPoset.preorder P) ⟦ delta→poset UnitDelta ⁎⟧' |i|
|i|-monotone {tt} {tt} tt⊑tt = record {}

|i|-monic : Injective (DeltaPoset.≈-setoid P) (preorder→setoid ⟦ delta→poset UnitDelta ⁎⟧') |i|
|i|-monic {tt} {tt} _ = PE.refl 

open DeltaPoset P
open import Data.List.Relation.Pointwise as PW
open import FreeSemilattice P renaming (⊥ to F⊥ ; _∨_ to _F∨_ ; _≈_ to _F≈_ )
open import Data.List.Any.Properties
open import Data.List.All

|f| : Bool → Σ[ l ∈ List ⊤ ] (IsFreeList l)
|f| false = [] , []-Free
|f| true = tt ∷ [] , (∷-Free tt [] [] ¬Any[] []-Free) 

|f|-≈ : (a b : Bool) → (a ≡ b) → (|f| a) F≈ (|f| b)
|f|-≈ a b a≡b@PE.refl = PW.refl PE.refl

|f|-⊥ : |f| false F≈ F⊥ 
|f|-⊥ = PW.refl PE.refl

|f|-∨ : (a b : Bool) → |f| (a B∨ b) F≈ (|f| a F∨ |f| b)
|f|-∨ false false = PW.refl PE.refl
|f|-∨ false true = PW.refl PE.refl
|f|-∨ true false = PW.refl PE.refl
|f|-∨ true true = PW.refl PE.refl

|g| : Σ[ l ∈ List ⊤ ] (IsFreeList l) → Bool
|g| ([] , []-Free) = false
|g| (tt ∷ [] , ∷-Free _ _ _ _ _) = true
|g| (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) = 
  ⊥-elim $ incomp (here (inj₁ $ DeltaPoset.reflexive P PE.refl))

|g|-≈ : (a b : SemilatCarrier) → a F≈ b → (|g| a) ≡ (|g| b)
|g|-≈ (.[] , []-Free) (.[] , []-Free) [] = PE.refl
|g|-≈ (ha ∷ [] , ∷-Free _ _ _ _ _) (hb ∷ [] , ∷-Free _ _ _ _ _) (ha≡hb ∷ []) = PE.refl
|g|-≈ (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) _ (ha≡hb ∷ _) = 
  ⊥-elim $ incomp $ here $ inj₁ (IsDecPartialOrder.refl ⊤≤-isDecPartialOrder)
|g|-≈ _ (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) (ha≡hb ∷ _) =
  ⊥-elim $ incomp $ here $ inj₁ (IsDecPartialOrder.refl ⊤≤-isDecPartialOrder)

|g|-⊥ : |g| F⊥ ≡ false 
|g|-⊥ = PE.refl

|g|-∨ : (a b : Σ[ l ∈ List ⊤ ] IsFreeList l) → (|g| (a F∨ b) ≡ (|g| a) B∨ (|g| b))
|g|-∨ ([] , []-Free) ([] , []-Free) = PE.refl
|g|-∨ (tt ∷ [] , ∷-Free _ _ _ _ _) ([] , []-Free) = PE.refl 
|g|-∨ ([] , []-Free) (tt ∷ [] , ∷-Free _ _ _ _ _) = PE.refl
|g|-∨ (tt ∷ [] , ∷-Free _ _ _ _ _) (tt ∷ [] , ∷-Free _ _ _ _ _) = PE.refl
|g|-∨ (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) _ = ⊥-elim $ incomp $ here (inj₁ $ DeltaPoset.reflexive P PE.refl) 
|g|-∨ _ (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) = ⊥-elim $ incomp $ here (inj₁ $ DeltaPoset.reflexive P PE.refl)

inv-S→FP→S : (a : Bool) → (|g| $ |f| a) ≡ a
inv-S→FP→S true = PE.refl
inv-S→FP→S false = PE.refl

inv-FP→S→FP : (a : Σ[ l ∈ List ⊤ ] IsFreeList l) → (|f| $ |g| a) F≈ a 
inv-FP→S→FP ([] , []-Free) = PW.refl PE.refl
inv-FP→S→FP (tt ∷ [] , ∷-Free _ _ _ _ _) = PW.refl PE.refl
inv-FP→S→FP (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) = ⊥-elim $ incomp $ here (inj₁ $ DeltaPoset.reflexive P PE.refl)

sem : SemSemilat l0 l0 l0 l0 l0 l0 l0 BoolSemilat
sem = record
  { S = S
  ; US = PE.refl
  ; P = P
  ; i = |i| , |i|-monotone , |i|-monic
  ; f = |f| , |f|-≈ , |f|-⊥ , |f|-∨
  ; g = |g| , |g|-≈ , |g|-⊥ , |g|-∨
  ; inv-S→FP→S = inv-S→FP→S
  ; inv-FP→S→FP = inv-FP→S→FP 
  }
