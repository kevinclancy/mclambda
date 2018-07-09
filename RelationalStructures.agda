module RelationalStructures where

open import Function using (_$_)
open import Relation.Nullary
open import Relation.Binary
open import Util
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.Lattice

open import Level

Preorder0 : Set₁
Preorder0 = Preorder l0 l0 l0

DecPoset0 : Set₁
DecPoset0 = DecPoset l0 l0 l0

StrictTotalOrder0 : Set₁
StrictTotalOrder0 = StrictTotalOrder l0 l0 l0

-- DeltaPoset : Set₁
-- DeltaPoset = Σ[ x ∈  DecPoset0 ] Σ[ y ∈ StrictTotalOrder0 ] (DecPoset.Carrier x ≡ StrictTotalOrder.Carrier y)

record DeltaPoset0 : Set l1 where
  infix  4 _≈_ _<_ _⊑_
  field
    Carrier                  : Set l0
    _≈_                      : Rel Carrier l0  -- The underlying equality.
    _⊑_                      : Rel Carrier l0  -- The partial order.
    _<_                      : Rel Carrier l0  -- The total order.
    isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_
    isDecPartialOrder  : IsDecPartialOrder _≈_ _⊑_

  open IsStrictTotalOrder isStrictTotalOrder public hiding(module Eq)
  open IsDecPartialOrder isDecPartialOrder public hiding (_≟_ ; module Eq) renaming (_≤?_ to _⊑?_)  

  module Eq = IsStrictTotalOrder.Eq isStrictTotalOrder

  -- incomparable
  _∥_ : Rel Carrier l0 
  a ∥ b = (¬ (a ⊑ b)) × (¬ (b ⊑ a))

  -- comparable
  _∦_ : Rel Carrier l0
  a ∦ b = (a ⊑ b) ⊎ (b ⊑ a)

  field    
    unimodality : {a b c d : Carrier} → (a < b) → (b < c) → (d ∦ a) → (d ∥ b) → (d ∥ c) 

  _∦?_ : (x : Carrier) → (y : Carrier) → Dec (x ∦ y)
  x ∦? y with x ⊑? y | y ⊑? x
  x ∦? y | yes x⊑y | _ = yes $ inj₁ x⊑y
  x ∦? y | no ¬x⊑y | yes y⊑x = yes $ inj₂ y⊑x
  x ∦? y | no ¬x⊑y | no ¬y⊑x = no z
    where
      z : ¬ ( x ⊑ y ⊎ y ⊑ x )
      z (inj₁ x⊑y) = ¬x⊑y x⊑y
      z (inj₂ y⊑x) = ¬y⊑x y⊑x

 
Semilat0 : Set₁
Semilat0 = BoundedJoinSemilattice l0 l0 l0

