module SemilatKinding.Core where

open import Util

open import Syntax
open import Kinding
open import BoolPoset

open import Level
open import FreeForgetfulAdjunction
open import RelationalStructures
open import SemDeltaPoset
open import SemPoset

open import Relation.Binary
open import Relation.Binary.Lattice
open import Function.Inverse
open import Data.Product
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality

record SemSemilat (cₛ ℓₛ₁ ℓₛ₂ cₚ ℓ⊑ₚ ℓ<ₚ ℓ~ₚ : Level) {τ τ₀ : τ} (isSemilat : IsSemilat τ τ₀)
                   : Set (Level.suc $ cₛ ⊔ ℓₛ₁ ⊔ ℓₛ₂ ⊔ cₚ ⊔ ℓ⊑ₚ ⊔ ℓ<ₚ ⊔ ℓ~ₚ) where
  field
    -- direct representation of semilattice
    S : BoundedJoinSemilattice l0 l0 l0
    
    US : (BoundedJoinSemilattice.poset S) ≡ ⟦ (semilat→poset isSemilat) ⁎⟧

    -- delta poset (freely generates S up-to-isomorphism)
    P : DeltaPoset {cₚ} {ℓ⊑ₚ} {ℓ<ₚ} {ℓ~ₚ}
    -- injection of τ₀ deltaPoset interpretation into P
    i : P ↣+ ⟦ semilat→delta isSemilat ⁑⟧ 
    -- factorization into free semilattice
    f : S ⇉ FP P
    -- defactorization out of free semilattice
    g : FP P ⇉ S
    -- f and g are inverses
    inv-S→FP→S : (a : BoundedJoinSemilattice.Carrier S) → (BoundedJoinSemilattice._≈_ S (proj₁ g $ proj₁ f $ a) a) 
    inv-FP→S→FP : (a : BoundedJoinSemilattice.Carrier $ FP P) → (BoundedJoinSemilattice._≈_ (FP P) (proj₁ f $ proj₁ g $ a) a) 
