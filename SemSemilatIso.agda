module SemSemilatIso where

open import SemilatKinding.Core public
open import Syntax
open import Kinding
open import SemKinding
open import Util

⟦_⁂iso⟧ : ∀ {τ τ₀ : τ} → (isSemilat : IsSemilat τ τ₀) → SemSemilatIso l0 l0 l0 l0 l0 l0 l0 isSemilat
⟦ NatSemilat ⁂iso⟧ = sem
  where 
    open import SemilatKinding.Nat
⟦ BoolSemilat ⁂iso⟧ = sem
  where
    open import SemilatKinding.Bool
⟦ ProductSemilat isSemilatL isSemilatR ⁂iso⟧ = sem
  where
    open import SemilatKinding.Product ⟦ isSemilatL ⁂iso⟧ ⟦ isSemilatR ⁂iso⟧  
⟦ PartialSemilat isSemilatContent ⁂iso⟧ = sem
  where
    open import SemilatKinding.Partial ⟦ isSemilatContent ⁂iso⟧

