open import Function using (_$_)
open import Function.Equivalence as FE
open import Function.Equality using (_⟨$⟩_)
open import Data.Empty
open import Data.List
open import Data.List.Properties as LP
open import Data.List.All as LA
open import Data.List.Any as LAny
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

module FreeSemilattice where

BoundedJoinSemilattice0 : Set₂
BoundedJoinSemilattice0 = BoundedJoinSemilattice l1 l0 l0

-- the space of monotone functions between delta posets P and R 
_→+_ : DeltaPoset0 → DeltaPoset0 → Set
P →+ R = Σ[ f ∈ (|P| → |R|) ] ∀ {p1 p2 : |P|} → p1 ⊑ₚ p2 → f p1 ⊑ᵣ f p2     
  where
    open DeltaPoset0 P renaming (_⊑_ to _⊑ₚ_ ; Carrier to |P|)
    open DeltaPoset0 R renaming (_⊑_ to _⊑ᵣ_ ; Carrier to |R|) 

-- the space of bounded join semilattice homomorphisms between bounded join semilattices S and T
_⇉_ : BoundedJoinSemilattice0 → BoundedJoinSemilattice0 → Set₁
S ⇉ T = Σ[ f ∈ (|S| → |T|)] ∀ {s1 s2 : |S|} → f (s1 ∨ₛ s2) ≡ (f s1) ∨ₜ (f s2) 
  where
    open BoundedJoinSemilattice S renaming (_∨_ to _∨ₛ_ ; Carrier to |S|)
    open BoundedJoinSemilattice T renaming (_∨_ to _∨ₜ_ ; Carrier to |T|)

-- the free semilattice functor's action on delta poset objects
FP : (P : DeltaPoset0) → BoundedJoinSemilattice0
FP P = FP-BJS
  where
    open import FreeSemilattice.Semilattice P

Ff : (P R : DeltaPoset0) → (f : P →+ R) → (FP P) ⇉ (FP R)
Ff P R (f , f+) = {!!}   
  where
    open BoundedJoinSemilattice (FP P) renaming (_∨_ to _∨ₚ_ ; Carrier to |FP|)
    open BoundedJoinSemilattice (FP R) renaming (_∨_ to _∨ᵣ_ ; Carrier to |FR|)

    |Ff| : |FP| → |FR|
    |Ff| (p , fp) = ?

