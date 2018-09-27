
module SemSemilat where

open import Syntax
open import Kinding
open import Util

open import SemilatKinding.Core

⟦_⁂⟧ : ∀ {τ τ₀ : τ} → (isSemilat : IsSemilat τ τ₀) → SemSemilat l0 l0 l0 l0 l0 l0 l0 isSemilat   
⟦ BoolSemilat ⁂⟧  = sem
  where
    open import SemilatKinding.Bool
⟦ NatSemilat ⁂⟧ = sem
  where
    open import SemilatKinding.Nat
⟦ ProductSemilat isSemilatL isSemilatR ⁂⟧ = sem
  where
    open import SemilatKinding.Product ⟦ isSemilatL ⁂⟧ ⟦ isSemilatR ⁂⟧
 
