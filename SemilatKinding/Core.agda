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
    f : (SemSemilatCore.S ⟦ isSemilat ⁂⟧) ⇉ FP (SemSemilatCore.P ⟦ isSemilat ⁂⟧)
    -- defactorization out of free semilattice
    g : FP (SemSemilatCore.P ⟦ isSemilat ⁂⟧) ⇉ (SemSemilatCore.S ⟦ isSemilat ⁂⟧) 
    -- f and g are inverses
    inv-S→FP→S : 
      (a : BoundedJoinSemilattice.Carrier (SemSemilatCore.S ⟦ isSemilat ⁂⟧)) → 
      (BoundedJoinSemilattice._≈_ (SemSemilatCore.S ⟦ isSemilat ⁂⟧) (proj₁ g $ proj₁ f $ a) a) 
    inv-FP→S→FP : 
      (a : BoundedJoinSemilattice.Carrier $ FP (SemSemilatCore.P ⟦ isSemilat ⁂⟧)) → 
      (BoundedJoinSemilattice._≈_ (FP (SemSemilatCore.P ⟦ isSemilat ⁂⟧)) (proj₁ f $ proj₁ g $ a) a) 
