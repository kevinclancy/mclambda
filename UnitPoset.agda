-- WARNING: this module shouldn't be necessary: instead, use Data.Unit.poset

module UnitPoset where

open import Function using (_∘_ ; _$_)

open import Data.Unit
open import Data.Nat hiding (_≟_)
open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import FinPoset
open import Util

private
  unitDepth : ⊤ → ℕ
  unitDepth tt = 0

  unitCovers : List $ Cover ⊤ unitDepth
  unitCovers = []

  module ⊤P = FinPoset.FinPoset ⊤ unitDepth unitCovers _≟_

_⊤≤_ : ⊤ → ⊤ → Set
_⊤≤_ = ⊤P._≤_

⊤≤-isPreorder : IsPreorder _≡_ _⊤≤_ 
⊤≤-isPreorder = ⊤P.≤-isPreorder

⊤≤-preorder : Preorder l0 l0 l0
⊤≤-preorder = ⊤P.≤-preorder

⊤≤-poset : Poset l0 l0 l0
⊤≤-poset = ⊤P.≤-poset

⊤≤-isPartialOrder : IsPartialOrder _≡_ _⊤≤_
⊤≤-isPartialOrder = ⊤P.≤-isPartialOrder

⊤≤-isDecPartialOrder : IsDecPartialOrder _≡_ _⊤≤_
⊤≤-isDecPartialOrder = ⊤P.≤-isDecPartialOrder

_⊤≟_ : Decidable _≡_
_⊤≟_ = IsDecPartialOrder._≟_ ⊤P.≤-isDecPartialOrder
