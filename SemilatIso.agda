module SemilatIso where

open import SemilatKinding.Core public
open import Syntax
open import Kinding
open import SemKinding
open import Util

⟦_Δiso⟧ : ∀ {τ τ₀ : τ} → (isSemilat : IsSemilat τ τ₀) → SemSemilatIso l0 l0 l0 l0 l0 l0 l0 isSemilat
⟦ NatSemilat Δiso⟧ = sem
  where 
    open import SemilatKinding.Nat
⟦ BoolSemilat Δiso⟧ = sem
  where
    open import SemilatKinding.Bool
⟦ ProductSemilat isSemilatL isSemilatR Δiso⟧ = sem
  where
    open import SemilatKinding.Product ⟦ isSemilatL Δiso⟧ ⟦ isSemilatR Δiso⟧  
⟦ PartialSemilat isSemilatContent Δiso⟧ = sem
  where
    open import SemilatKinding.Partial ⟦ isSemilatContent Δiso⟧   
⟦ IVarSemilat isStosetContent Δiso⟧ = sem
  where
    open import SemilatKinding.IVar
⟦ DictSemilat isStosetDom isSemilatCod Δiso⟧ = sem
  where
    postulate sem : SemSemilatIso l0 l0 l0 l0 l0 l0 l0 (DictSemilat isStosetDom isSemilatCod)
