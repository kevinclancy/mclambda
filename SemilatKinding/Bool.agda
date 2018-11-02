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
open import FreeForgetfulAdjunction
open import BoolPoset
open import FinPoset
open import SemKinding

semilatCore = ⟦ BoolSemilat ⁂⟧

P : DeltaPoset {l0} {l0} {l0} {l0}
P = SemSemilatCore.P semilatCore 

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

sem : SemSemilatIso l0 l0 l0 l0 l0 l0 l0 BoolSemilat
sem = record
  { f = |f| , |f|-≈ , |f|-⊥ , |f|-∨
  ; g = |g| , |g|-≈ , |g|-⊥ , |g|-∨
  ; inv-S→FP→S = inv-S→FP→S
  ; inv-FP→S→FP = inv-FP→S→FP 
  }
