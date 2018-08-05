open import Data.List
open import Data.List.All
open import Data.List.Any
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE

open import RelationalStructures
open import Util

module FreeSemilattice (P : DeltaPoset0) where

import FreeSemilattice.Core P as Core
import FreeSemilattice.Poset P as Pos
import FreeSemilattice.Semilattice P as Semilat

DeltaCarrier : Set
DeltaCarrier = DeltaPoset0.Carrier P

FP-BJS : BoundedJoinSemilattice l1 l0 l0
FP-BJS = Semilat.FP-BJS

SemilatCarrier : Set₁
SemilatCarrier = BoundedJoinSemilattice.Carrier Semilat.FP-BJS

_⊑_ : Rel DeltaCarrier l0
_⊑_ = DeltaPoset0._⊑_ P

_<_ : Rel DeltaCarrier l0
_<_ = DeltaPoset0._<_ P

_∦_ : Rel DeltaCarrier l0
_∦_ = DeltaPoset0._∦_ P

_∥_ : Rel DeltaCarrier l0
_∥_ = DeltaPoset0._∥_ P

_≈_ : Rel SemilatCarrier l0
_≈_ = Core._≈_

_≤_ : Rel SemilatCarrier l0
_≤_ = BoundedJoinSemilattice._≤_ FP-BJS

⊥ : SemilatCarrier
⊥ = BoundedJoinSemilattice.⊥ FP-BJS

_⊔_ : List DeltaCarrier → List DeltaCarrier → List DeltaCarrier
_⊔_ = Core._∨_

_∨_ : SemilatCarrier → SemilatCarrier → SemilatCarrier
_∨_ = BoundedJoinSemilattice._∨_ FP-BJS

∨-free : {l1 l2 : List DeltaCarrier} → Core.IsFreeList _<_ _⊑_ l1 → Core.IsFreeList _<_ _⊑_ l2 → 
          Core.IsFreeList _<_ _⊑_ (l1 ⊔ l2)  
∨-free = Core.∨-free


[]-Free : Core.IsFreeList _<_ _⊑_ []
[]-Free = Core.[]-Free
 
∷-Free : (h : DeltaCarrier) → (t : List DeltaCarrier) → (All (h <_) t) → ¬ (Any (h ∦_) t) → 
           Core.IsFreeList _<_ _⊑_ t → Core.IsFreeList _<_ _⊑_ (h ∷ t)  
∷-Free = Core.∷-Free
