open import Relation.Binary
open import Relation.Binary.Lattice

open import Util

module IVar (E : StrictTotalOrder l0 l0 l0) where

|E| = StrictTotalOrder.Carrier E
_<E_ = StrictTotalOrder._<_ E
_≈E_ = StrictTotalOrder._≈_ E
≈E-setoid = StrictTotalOrder.Eq.setoid E
trans-≈E = StrictTotalOrder.Eq.trans E

open import DiscreteDelta E
open import FreeSemilattice (deltaPoset) public

⌈⌉-semilat : BoundedJoinSemilattice l0 l0 l0
⌈⌉-semilat = FP-BJS 

⌈⌉-poset : Poset l0 l0 l0
⌈⌉-poset = BoundedJoinSemilattice.poset ⌈⌉-semilat

⌈⌉-Ty : Set 
⌈⌉-Ty = BoundedJoinSemilattice.Carrier ⌈⌉-semilat
