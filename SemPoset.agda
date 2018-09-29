
module SemPoset where


open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Data.Sum
open import Data.Product

open import Syntax
open import Kinding
open import Util
open import SemScalars

⟦_⁎⟧ : ∀ {τ : τ} → IsPoset τ → Poset l0 l0 l0
⟦ FunPoset {q = q} domIsPoset codIsPoset ⁎⟧ = ⇒-poset (⟦ q q⟧ ⟦ domIsPoset ⁎⟧) ⟦ codIsPoset ⁎⟧  
  where
    open import Posets
⟦ ProductPoset isPosetL isPosetR ⁎⟧ = ×-poset ⟦ isPosetL ⁎⟧ ⟦ isPosetR ⁎⟧  
  where
    open import Data.Product
    open import Data.Product.Relation.Pointwise.NonDependent
⟦ SumPoset isPosetL isPosetR ⁎⟧ = ⊎-poset {l0} {l0} {l0} {l0} {l0} {l0} ⟦ isPosetL ⁎⟧ ⟦ isPosetR ⁎⟧  
  where
    open import Data.Sum
    open import Data.Sum.Relation.Pointwise
⟦ UnitPoset ⁎⟧ = poset
  where
    open import Data.Unit
⟦ BoolPoset ⁎⟧ = B≤-poset
  where
    open import BoolPoset
⟦ NatPoset ⁎⟧ = record 
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _≤_ = _≤_ 
  ; isPartialOrder = ≤-isPartialOrder
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties
