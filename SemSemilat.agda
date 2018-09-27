
module SemSemilat where

open import Function using (_$_ ; _|>′_ ; const)
open import Function.Equivalence  
open import Function.Equality using (_⟨$⟩_) 
open import Syntax
open import Kinding
open import BoolPoset
open import Relation.Nullary
open import Relation.Binary
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.List
open import Data.List.Properties as LP
open import Data.List.Any as LAny
open import Data.List.All as LA
open import Level
open import Util using (l0;l1;l2)
open import Data.Unit renaming (preorder to unitPreorder ; decTotalOrder to unitToset) hiding (_≤_)
open import Data.Nat as N hiding (_<_ ; _⊔_)
open import Data.Nat.Properties as NP
open import Data.Bool
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
open import SemDeltaPoset
open import FreeForgetfulAdjunction
open import RelationalStructures
open Util

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
 
