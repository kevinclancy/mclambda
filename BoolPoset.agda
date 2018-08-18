module BoolPoset where

open import Function using (_∘_ ; _$_)

open import Data.Bool
open import Data.Nat hiding (_≟_)
open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
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

