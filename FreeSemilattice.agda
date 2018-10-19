open import Data.List
open import Data.List.All
open import Data.List.Any
open import Data.Product
open import Data.Sum
open import Function using (_$_)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE hiding (preorder)
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

preorder : Preorder _ _ _
preorder = BoundedJoinSemilattice.preorder FP-BJS

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

⊑-trans : Transitive _⊑_
⊑-trans = DeltaPoset.trans⊑ P

⊑-respˡ-≈ :  _⊑_ Respectsˡ _~_
⊑-respˡ-≈ = DeltaPoset.⊑-respˡ-≈ P

⊑-respʳ-≈ :  _⊑_ Respectsʳ _~_
⊑-respʳ-≈ = DeltaPoset.⊑-respʳ-≈ P

⊑-decPoset : DecPoset _ _ _ 
⊑-decPoset = record 
  { Carrier = DeltaCarrier
  ; _≈_ = _~_
  ; _≤_ = _⊑_
  ; isDecPartialOrder = DeltaPoset.isDecPartialOrder P
  }

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

≈-trans : Transitive _≈_
≈-trans {i} {j} {k} i≈j j≈k = SemilatEq.trans {i} {j} {k} i≈j j≈k

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

∨-identityʳ : RightIdentity _≈_ ⊥ _∨_
∨-identityʳ = identityʳ

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

p∈c1≈c2 : {p : DeltaCarrier} → {c1 c2 : SemilatCarrier} → c1 ≈ c2 → p ∈ c1 → p ∈ c2
p∈c1≈c2 {p} {c1@(l1 , f1)} {c2@(l2 , f2)} c1≈c2 p∈c1 = Core.a∈l1~l2 {p} {l1} {l2} c1≈c2 p∈c1

P∨ : {l1 l2 : List DeltaCarrier} → (f1 : IsFreeList l1) → (f2 : IsFreeList l2) → 
      (a : DeltaCarrier) → Set _
P∨ {l1} {l2} f1 f2 a = (a ∈' l1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈' l2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈' l1 × a ∈' l2)

x∈∨⇔P∨ : (c1 c2 c3 : SemilatCarrier) → 
            (eq : (c1 ∨ c2) ≈ c3) → (x : DeltaCarrier) → (x ∈ c3 ⇔ P∨ (proj₂ c1) (proj₂ c2) x)

x∈∨⇔P∨ (l1 , f1) (l2 , f2) (l3 , f3) eq x = Core.x∈∨⇔P∨ f1 f2 f3 eq x

concat-F : (a : SemilatCarrier) → (b : SemilatCarrier) → 
            (All (λ x → All (x <_) $ proj₁ b) $ proj₁ a) →
            (All (λ x → All (x ∥_) $ proj₁ b) $ proj₁ a) → 
            Σ[ c ∈ SemilatCarrier ] proj₁ c ≡ (proj₁ a) ++ (proj₁ b) 
concat-F = Core.concat-FP
