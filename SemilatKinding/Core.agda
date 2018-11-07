module SemilatKinding.Core where

open import Util

open import Syntax
open import Kinding
open import BoolPoset

open import Level
open import FreeForgetfulAdjunction
open import Deltas
open import SemKinding

open import Relation.Binary
open import Relation.Binary.Lattice
open import Function.Inverse
open import Data.Product
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality

record SemSemilatIso (cₛ ℓₛ₁ ℓₛ₂ cₚ ℓ⊑ₚ ℓ<ₚ ℓ~ₚ : Level) {τ τ₀ : τ} (isSemilat : IsSemilat τ τ₀)
                     : Set (Level.suc $ cₛ ⊔ ℓₛ₁ ⊔ ℓₛ₂ ⊔ cₚ ⊔ ℓ⊑ₚ ⊔ ℓ<ₚ ⊔ ℓ~ₚ) where
  field
    -- factorization into free semilattice
    f : (SemSemilatCore.S ⟦ isSemilat Δ⟧) ⇉ FP (SemSemilatCore.P ⟦ isSemilat Δ⟧)
    -- defactorization out of free semilattice
    g : FP (SemSemilatCore.P ⟦ isSemilat Δ⟧) ⇉ (SemSemilatCore.S ⟦ isSemilat Δ⟧) 
    -- f and g are inverses
    inv-S→FP→S : 
      (a : BoundedJoinSemilattice.Carrier (SemSemilatCore.S ⟦ isSemilat Δ⟧)) → 
      (BoundedJoinSemilattice._≈_ (SemSemilatCore.S ⟦ isSemilat Δ⟧) (proj₁ g $ proj₁ f $ a) a) 
    inv-FP→S→FP : 
      (a : BoundedJoinSemilattice.Carrier $ FP (SemSemilatCore.P ⟦ isSemilat Δ⟧)) → 
      (BoundedJoinSemilattice._≈_ (FP (SemSemilatCore.P ⟦ isSemilat Δ⟧)) (proj₁ f $ proj₁ g $ a) a) 
