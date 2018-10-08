-- this should be renamed to just Bool, since it has other things besides a poset ordering

module BoolPoset where

open import Function using (_∘_ ; _$_)

open import Data.Bool
open import Data.Nat hiding (_≟_)
open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Nullary
open import FinPoset
open import Util

private
  boolDepth : Bool → ℕ
  boolDepth false = 1
  boolDepth true = 0

  boolCovers : List $ Cover Bool boolDepth
  boolCovers = [ false / true / ≤′-refl ]

  module BP = FinPoset.FinPoset Bool boolDepth boolCovers _≟_

infix 4 _B≤_
infixr 6 _B∨_

_B≤_ : Bool → Bool → Set
_B≤_ = BP._≤_

B≤-isPreorder : IsPreorder _≡_ _B≤_ 
B≤-isPreorder = BP.≤-isPreorder

B≤-preorder : Preorder l0 l0 l0
B≤-preorder = BP.≤-preorder

B≤-isPartialOrder : IsPartialOrder _≡_ _B≤_
B≤-isPartialOrder = BP.≤-isPartialOrder

B≤-poset : Poset l0 l0 l0
B≤-poset = BP.≤-poset

_B∨_ : Bool → Bool → Bool
true B∨ true = true
true B∨ false = true
false B∨ true = true
false B∨ false = false

data _B<_ : Bool → Bool → Set where
  f<t : false B< true

B<-transitive : Transitive _B<_
B<-transitive f<t ()

B<-compare : Trichotomous _≡_ _B<_
B<-compare false false = tri≈ (λ ()) PE.refl (λ ())
B<-compare false true = tri< f<t (λ ()) (λ ())
B<-compare true false = tri> (λ ()) (λ ()) f<t
B<-compare true true = tri≈ (λ ()) PE.refl (λ ())

B<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _B<_
B<-isStrictTotalOrder = 
  record
  { isEquivalence = PE.isEquivalence
  ; trans = B<-transitive
  ; compare = B<-compare
  } 

B<-strictTotalOrder : StrictTotalOrder l0 l0 l0
B<-strictTotalOrder =
  record
  { Carrier = Bool
  ; _≈_ = _≡_
  ; _<_ = _B<_
  ; isStrictTotalOrder = B<-isStrictTotalOrder
  }
