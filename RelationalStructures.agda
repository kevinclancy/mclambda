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
open import Relation.Binary.PartialOrderReasoning

open import Level

Preorder0 : Set₁
Preorder0 = Preorder l0 l0 l0

DecPoset0 : Set₁
DecPoset0 = DecPoset l0 l0 l0

StrictTotalOrder0 : Set₁
StrictTotalOrder0 = StrictTotalOrder l0 l0 l0

record DeltaPoset {c ℓ⊑ ℓ< ℓ≈ : Level} : Set (Level.suc $ c ⊔ ℓ⊑ ⊔ ℓ< ⊔ ℓ≈) where
  infix  4 _<_ _⊑_
  field
    Carrier                  : Set c
    _⊑_                      : Rel Carrier ℓ⊑  -- The partial order.
    _<_                      : Rel Carrier ℓ<  -- The total order.
    _≈_                      : Rel Carrier ℓ≈  -- The underlying equivalence, shared by partial and total orders.
    isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_
    isDecPartialOrder  : IsDecPartialOrder _≈_ _⊑_

  open IsStrictTotalOrder isStrictTotalOrder public hiding(module Eq)
  open IsDecPartialOrder isDecPartialOrder public hiding (_≟_ ; module Eq) renaming (_≤?_ to _⊑?_)  

  module Eq = IsStrictTotalOrder.Eq isStrictTotalOrder

  trans⊑ : Transitive _⊑_
  trans⊑ = IsDecPartialOrder.trans isDecPartialOrder

  trans< : Transitive _<_
  trans< = IsStrictTotalOrder.trans isStrictTotalOrder

  trans≈ : Transitive _≈_
  trans≈ = IsDecEquivalence.trans isDecEquivalence

  sym≈ : Symmetric _≈_
  sym≈ = IsDecEquivalence.sym isDecEquivalence

  refl≈ : Reflexive _≈_
  refl≈ = IsDecEquivalence.refl isDecEquivalence

  ≈-decSetoid : DecSetoid c ℓ≈
  ≈-decSetoid =
    record
    { Carrier = Carrier
    ; _≈_ = _≈_
    ; isDecEquivalence = isDecEquivalence
    }

  _≈?_ = _≟_

  _∦_ : Rel Carrier ℓ⊑
  a ∦ b = (a ⊑ b) ⊎ (b ⊑ a)

  -- incomparable
  _∥_ : Rel Carrier ℓ⊑ 
  a ∥ b = ¬ (a ∦ b)

  field    
    unimodality : {a b c d : Carrier} → (a < b) → (b < c) → (d ∦ a) → (d ∥ b) → (d ∥ c) 

  -- comparable
  data Comparison : Carrier → Carrier → Set (ℓ⊑ ⊔ ℓ≈) where
    l⊑r : {l r : Carrier} → (l ⊑ r) → ¬ (r ⊑ l) → Comparison l r
    r⊑l : {l r : Carrier} → ¬ (l ⊑ r) → (r ⊑ l) → Comparison l r
    l≈r : {l r : Carrier} → (l ≈ r) → Comparison l r 
    l∥r : {l r : Carrier} → (l ∥ r) → Comparison l r

  ∦-sym : {a b : Carrier} → (a ∦ b) → (b ∦ a)
  ∦-sym (inj₁ x) = inj₂ x
  ∦-sym (inj₂ x) = inj₁ x

  ∥-sym : {a b : Carrier} → (a ∥ b) → (b ∥ a)
  ∥-sym p b∦a = p (∦-sym b∦a)

  ∥⇒¬≈ : {a b : Carrier} → (a ∥ b) → (a ≈ b) → ⊥
  ∥⇒¬≈ {a} {b} a∥b a≈b = a∥b (inj₁ a⊑b)
    where
      a⊑b : a ⊑ b
      a⊑b = reflexive a≈b

  ∦-refl : (x : Carrier) → x ∦ x
  ∦-refl x = inj₁ refl

  _∦?_ : (x : Carrier) → (y : Carrier) → Comparison x y
  x ∦? y with x ⊑? y | y ⊑? x
  x ∦? y | yes x⊑y | yes y⊑x = l≈r (antisym x⊑y y⊑x)
  x ∦? y | yes x⊑y | no ¬y⊑x = l⊑r x⊑y ¬y⊑x
  x ∦? y | no ¬x⊑y | yes y⊑x = r⊑l ¬x⊑y y⊑x
  x ∦? y | no ¬x⊑y | no ¬y⊑x = l∥r z
    where
      z : ¬ ( x ⊑ y ⊎ y ⊑ x )
      z (inj₁ x⊑y) = ¬x⊑y x⊑y
      z (inj₂ y⊑x) = ¬y⊑x y⊑x
  
  ∦-resp-≈ˡ : {a b c : Carrier} → (a ∦ c) → (a ≈ b) → (b ∦ c)
  ∦-resp-≈ˡ (inj₁ a⊑c) a≈b = inj₁ $ trans⊑ (reflexive $ sym≈ a≈b) a⊑c
  ∦-resp-≈ˡ (inj₂ c⊑a) a≈b = inj₂ $ trans⊑ c⊑a (reflexive a≈b)

  ∦-resp-≈ʳ : {a b c : Carrier} → (c ∦ a) → (a ≈ b) → (c ∦ b)
  ∦-resp-≈ʳ (inj₁ c⊑a) a≈b = inj₁ $ trans⊑ c⊑a (reflexive a≈b)
  ∦-resp-≈ʳ (inj₂ a⊑c) a≈b = inj₂ $ trans⊑ (reflexive $ sym≈ a≈b) a⊑c 
 
  ⊑-respʳ-≈ = ≤-respʳ-≈ 
  ⊑-respˡ-≈ = ≤-respˡ-≈

Semilat0 : Set₁
Semilat0 = BoundedJoinSemilattice l0 l0 l0

