open import Data.List
open import Data.List.All
open import Data.List.Any
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE
open import Level renaming (_⊔_ to _v_) 
open import Function.Equivalence as FE
open import Algebra.FunctionProperties
open import RelationalStructures
open import Util

module FreeSemilattice {c ℓ⊑ ℓ< ℓ≈} (P : DeltaPoset {c} {ℓ⊑} {ℓ<} {ℓ≈}) where

import FreeSemilattice.Core P as Core 
import FreeSemilattice.Poset P as Pos 
import FreeSemilattice.Semilattice P as Semilat

infixl 4 _∨_
infix 6 _≈_

DeltaCarrier : Set _
DeltaCarrier = DeltaPoset.Carrier P

SemilatCarrier : Set _
SemilatCarrier = BoundedJoinSemilattice.Carrier Semilat.FP-BJS

FP-BJS : BoundedJoinSemilattice _ _ _
FP-BJS = Semilat.FP-BJS

FP-JS : JoinSemilattice _ _ _
FP-JS = record
  { Carrier = SemilatCarrier
  ; _≈_ = BoundedJoinSemilattice._≈_ FP-BJS
  ; _≤_ = BoundedJoinSemilattice._≤_ FP-BJS
  ; _∨_ = BoundedJoinSemilattice._∨_ FP-BJS
  ; isJoinSemilattice = record 
    { isPartialOrder = IsJoinSemilattice.isPartialOrder (BoundedJoinSemilattice.isJoinSemilattice FP-BJS)
    ; supremum = BoundedJoinSemilattice.supremum FP-BJS }
  }

open import Relation.Binary.Properties.BoundedJoinSemilattice FP-BJS
open import Relation.Binary.Properties.JoinSemilattice FP-JS renaming (∨-assoc to ∨-assoc' ; ∨-comm to ∨-comm')
module SemilatEq = BoundedJoinSemilattice.Eq FP-BJS

_⊑_ : Rel DeltaCarrier _
_⊑_ = DeltaPoset._⊑_ P

_~_ : Rel DeltaCarrier _
_~_ = DeltaPoset._≈_ P

⊑-refl : Reflexive _⊑_
⊑-refl {x} = (DeltaPoset.refl P) {x}

⊑-reflexive : _~_ ⇒ _⊑_
⊑-reflexive = DeltaPoset.reflexive⊑ P 

_<_ : Rel DeltaCarrier _
_<_ = DeltaPoset._<_ P

_≈_ : Rel SemilatCarrier _
_≈_ = Core._≈_

≈-refl : Reflexive _≈_
≈-refl {x} = SemilatEq.refl {x}

≈-sym : Symmetric _≈_
≈-sym {i} {j} = SemilatEq.sym {i} {j}

≈-reflexive : _≡_ ⇒ _≈_
≈-reflexive = SemilatEq.reflexive 

FP-setoid : Setoid _ _
FP-setoid = Core.FP-Setoid

_∦_ : Rel DeltaCarrier _
_∦_ = DeltaPoset._∦_ P

_∥_ : Rel DeltaCarrier _
_∥_ = DeltaPoset._∥_ P

_≤_ : Rel SemilatCarrier _
_≤_ = BoundedJoinSemilattice._≤_ FP-BJS

⊥ : SemilatCarrier
⊥ = BoundedJoinSemilattice.⊥ FP-BJS

_⊔_ : List DeltaCarrier → List DeltaCarrier → List DeltaCarrier
_⊔_ = Core._∨_

_∨_ : SemilatCarrier → SemilatCarrier → SemilatCarrier
_∨_ = BoundedJoinSemilattice._∨_ FP-BJS

∨-congˡ : {c1 c2 : SemilatCarrier} → (c3 : SemilatCarrier) → c1 ≈ c2 → (c1 ∨ c3) ≈ (c2 ∨ c3)
∨-congˡ {c1} {c2} c3 c1≈c2 = ∨-cong {c1} {c2} {c3} {c3} c1≈c2 (≈-refl {x = c3}) 

∨-congʳ : {c1 c2 : SemilatCarrier} → (c3 : SemilatCarrier) → c1 ≈ c2 → (c3 ∨ c1) ≈ (c3 ∨ c2)
∨-congʳ {c1} {c2} c3 c1≈c2 = ∨-cong {c3} {c3} {c1} {c2} (≈-refl {x = c3}) c1≈c2 

∨-identityˡ : LeftIdentity _≈_ ⊥ _∨_
∨-identityˡ = identityˡ

∨-identityʳ : LeftIdentity _≈_ ⊥ _∨_
∨-identityʳ = identityˡ

∨-assoc : Associative _≈_ _∨_
∨-assoc = ∨-assoc'

∨-comm : Commutative _≈_ _∨_
∨-comm = ∨-comm'

IsFreeList : List DeltaCarrier → Set _
IsFreeList = Core.IsFreeList

-- gives us the constructors []-Free and ∷-Free
open Core.IsFreeList public

sng-free : {c : DeltaCarrier} → (Core.IsFreeList (c ∷ []))
sng-free = Core.sng-free

module _ where
  open import Data.List.Membership.Setoid (DeltaPoset.≈-setoid P) renaming (_∈_ to _∈'_) public
  
  _∈_ : DeltaCarrier → SemilatCarrier → Set _
  p ∈ (l , f) = p ∈' l

c1≈c2⇔sameElements : (c1 c2 : SemilatCarrier) → (c1 ≈ c2) ⇔ (∀ (a : DeltaCarrier) → (a ∈ c1) ⇔ (a ∈ c2))
c1≈c2⇔sameElements c1 c2 = Core.l1~l2⇔sameElements c1 c2  


