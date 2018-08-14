open import Data.List
open import Data.List.All
open import Data.List.Any
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE
open import Level renaming (_⊔_ to _v_) 

open import RelationalStructures
open import Util

module FreeSemilattice {c ℓ⊑ ℓ< ℓ≈} (P : DeltaPoset {c} {ℓ⊑} {ℓ<} {ℓ≈}) where

import FreeSemilattice.Core P as Core 
import FreeSemilattice.Poset P as Pos 
import FreeSemilattice.Semilattice P as Semilat

DeltaCarrier : Set _
DeltaCarrier = DeltaPoset.Carrier P

SemilatCarrier : Set _
SemilatCarrier = BoundedJoinSemilattice.Carrier Semilat.FP-BJS

FP-BJS : BoundedJoinSemilattice _ _ _
FP-BJS = Semilat.FP-BJS

_⊑_ : Rel DeltaCarrier _
_⊑_ = DeltaPoset._⊑_ P

_<_ : Rel DeltaCarrier _
_<_ = DeltaPoset._<_ P

_≈_ : Rel SemilatCarrier _
_≈_ = Core._≈_

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

-- gives us the constructors []-Free and ∷-Free
open Core.IsFreeList public

sng-free : {c : DeltaCarrier} → (Core.IsFreeList (c ∷ []))
sng-free = Core.sng-free

