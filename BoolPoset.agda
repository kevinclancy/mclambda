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

_B≤_ : Bool → Bool → Set
_B≤_ = BP._≤_

B≤-isPreorder : IsPreorder _≡_ _B≤_ 
B≤-isPreorder = BP.≤-isPreorder

B≤-preorder : Preorder l0 l0 l0
B≤-preorder = BP.≤-preorder

B≤-poset : Poset l0 l0 l0
B≤-poset = BP.≤-poset

