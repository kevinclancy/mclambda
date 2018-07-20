open import Function using (_$_)
open import Data.Empty
open import Data.List
open import Data.List.All as LA
open import Data.List.Any
open import Data.List.Any.Properties as LAP
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE
open import RelationalStructures
open import Util

module FreeSemilattice (P : DeltaPoset0) where

open DeltaPoset0 P renaming (trans to tran)

data IsFreeList {A : Set l0} (_<_ : Rel A l0) (_⊑_ : Rel A l0) : List A → Set l1 where
  []-Free : IsFreeList _<_ _⊑_ []
  ∷-Free : (hd : A) → (tl : List A) → (All (hd <_) tl) → ¬ (Any (λ x → (hd ⊑ x) ⊎ (x ⊑ hd)) tl) → 
            (IsFreeList _<_ _⊑_ tl) → IsFreeList _<_ _⊑_ (hd ∷ tl) 

Carrier-FP : Set₁
Carrier-FP = Σ[ x ∈ List Carrier ] (IsFreeList _<_ _⊑_ x)

data _≤_ : Carrier-FP → Carrier-FP → Set₁ where
  []-≤ : {cfp : Carrier-FP} → ([] , []-Free) ≤ cfp  
  cmp-≤ : {c d : Carrier} {c' d' : List Carrier} → (c'-free : IsFreeList _<_ _⊑_ c') →
          (cc'-free : IsFreeList _<_ _⊑_ (c ∷ c')) →
          (dd'-free : IsFreeList _<_ _⊑_ (d ∷ d')) →
          c ⊑ d →
          (c' , c'-free) ≤ (d ∷ d' , dd'-free) →
          (c ∷ c' , cc'-free) ≤ (d ∷ d' , dd'-free)
  skip-≤ : {c d : Carrier} {c' d' : List Carrier} → 
            (cc'-free : IsFreeList _<_ _⊑_ (c ∷ c')) → 
            (d'-free : IsFreeList _<_ _⊑_ d') → 
            (dd'-free : IsFreeList _<_ _⊑_ (d ∷ d')) →
            (d < c) → (c ∥ d) → (c ∷ c' , cc'-free) ≤ (d' , d'-free) →
            (c ∷ c' , cc'-free) ≤ (d ∷ d' , dd'-free)
