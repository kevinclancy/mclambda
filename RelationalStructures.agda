module RelationalStructures where

open import Data.Empty
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
  infix  4 _<_ _⊑_
  field
    Carrier                  : Set l0
    _⊑_                      : Rel Carrier l0  -- The partial order.
    _<_                      : Rel Carrier l0  -- The total order.
    isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
    isDecPartialOrder  : IsDecPartialOrder _≡_ _⊑_

  open IsStrictTotalOrder isStrictTotalOrder public hiding(module Eq)
  open IsDecPartialOrder isDecPartialOrder public hiding (_≟_ ; module Eq) renaming (_≤?_ to _⊑?_)  

  module Eq = IsStrictTotalOrder.Eq isStrictTotalOrder

  transitive⊑ : Transitive _⊑_
  transitive⊑ = IsDecPartialOrder.trans isDecPartialOrder

  transitive< : Transitive _<_
  transitive< = IsStrictTotalOrder.trans isStrictTotalOrder

  _∦_ : Rel Carrier l0
  a ∦ b = (a ⊑ b) ⊎ (b ⊑ a)

  -- incomparable
  _∥_ : Rel Carrier l0 
  a ∥ b = ¬ (a ∦ b)

  field    
    unimodality : {a b c d : Carrier} → (a < b) → (b < c) → (d ∦ a) → (d ∥ b) → (d ∥ c) 

  -- comparable
  data Comparison : Carrier → Carrier → Set where
    l⊑r : {l r : Carrier} → (l ⊑ r) → ¬ (r ⊑ l) → Comparison l r
    r⊑l : {l r : Carrier} → ¬ (l ⊑ r) → (r ⊑ l) → Comparison l r
    l≡r : {l r : Carrier} → (l ≡ r) → Comparison l r 
    l∥r : {l r : Carrier} → (l ∥ r) → Comparison l r

  ∦-sym : {a b : Carrier} → (a ∦ b) → (b ∦ a)
  ∦-sym (inj₁ x) = inj₂ x
  ∦-sym (inj₂ x) = inj₁ x

  ∥-sym : {a b : Carrier} → (a ∥ b) → (b ∥ a)
  ∥-sym p b∦a = p (∦-sym b∦a)

  ∥⇒¬≈ : {a b : Carrier} → (a ∥ b) → (a ≡ b) → ⊥
  ∥⇒¬≈ {a} {b} a∥b a≡b = a∥b (inj₁ a⊑b)
    where
      a⊑b : a ⊑ b
      a⊑b = reflexive a≡b

  ∦-refl : (x : Carrier) → x ∦ x
  ∦-refl x = inj₁ refl

  _∦?_ : (x : Carrier) → (y : Carrier) → Comparison x y
  x ∦? y with x ⊑? y | y ⊑? x
  x ∦? y | yes x⊑y | yes y⊑x = l≡r (antisym x⊑y y⊑x)
  x ∦? y | yes x⊑y | no ¬y⊑x = l⊑r x⊑y ¬y⊑x
  x ∦? y | no ¬x⊑y | yes y⊑x = r⊑l ¬x⊑y y⊑x
  x ∦? y | no ¬x⊑y | no ¬y⊑x = l∥r z
    where
      z : ¬ ( x ⊑ y ⊎ y ⊑ x )
      z (inj₁ x⊑y) = ¬x⊑y x⊑y
      z (inj₂ y⊑x) = ¬y⊑x y⊑x

 
Semilat0 : Set₁
Semilat0 = BoundedJoinSemilattice l0 l0 l0

