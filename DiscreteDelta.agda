open import RelationalStructures 
open import Relation.Binary
open import Relation.Nullary
open import Data.Sum
open import Function using (_$_)

module DiscreteDelta {c ℓ≈ ℓ<} (sto : StrictTotalOrder c ℓ≈ ℓ<) where

|C| = StrictTotalOrder.Carrier sto
_≈₀_ = StrictTotalOrder._≈_ sto
≈-setoid = StrictTotalOrder.decSetoid sto
_≟₀_ = StrictTotalOrder._≟_ sto
_<₀_ = StrictTotalOrder._<_ sto
irrefl< = StrictTotalOrder.irrefl sto
trans< = StrictTotalOrder.trans sto
sym≈ = DecSetoid.sym ≈-setoid

data _⊑₀_ : |C| → |C| → Set ℓ≈ where
  ⊑-refl : {c0 c1 : |C|} → (c0 ≈₀ c1) → c0 ⊑₀ c1

trans-⊑ : {a b c : |C|} → a ⊑₀ b → b ⊑₀ c → a ⊑₀ c
trans-⊑ (⊑-refl a≈b) (⊑-refl b≈c) = ⊑-refl $ (DecSetoid.trans ≈-setoid) a≈b b≈c

antisym-⊑ : {a b : |C|} → a ⊑₀ b → b ⊑₀ a → a ≈₀ b
antisym-⊑ (⊑-refl a≈b) (⊑-refl b≈a) = a≈b

_⊑?_ : Decidable _⊑₀_
a ⊑? b with a ≟₀ b
a ⊑? b | yes a≈b = yes $ ⊑-refl a≈b
a ⊑? b | no ¬a≈b = no ¬a⊑b 
  where
    ¬a⊑b : ¬ (a ⊑₀ b)
    ¬a⊑b (⊑-refl a≈b) = ¬a≈b a≈b
    
_∦₀_ : |C| → |C| → Set _
a ∦₀ b = a ⊑₀ b ⊎ b ⊑₀ a

_∥₀_ : |C| → |C| → Set _
a ∥₀ b = ¬ (a ∦₀ b)

unimodality : {a b c : |C|} → a <₀ b → b <₀ c → a ∥₀ b → b ∥₀ c → a ∥₀ c
unimodality a<b b<c a∥b b∥c (inj₁ (⊑-refl a≈c)) = irrefl< a≈c (trans< a<b b<c)
unimodality a<b b<c a∥b b∥c (inj₂ (⊑-refl c≈a)) = irrefl< (sym≈ c≈a) (trans< a<b b<c)

deltaPoset = record
  { Carrier = |C| 
  ; _⊑_ = _⊑₀_
  ; _<_ = _<₀_
  ; _≈_ = _≈₀_
  ; isStrictTotalOrder = StrictTotalOrder.isStrictTotalOrder sto
  ; isDecPartialOrder = record
    { isPartialOrder = record
      { isPreorder = record
          { isEquivalence = StrictTotalOrder.isEquivalence sto
          ; reflexive = ⊑-refl
          ; trans = trans-⊑
          }
      ; antisym = antisym-⊑
      }
      ; _≟_ = _≟₀_
      ; _≤?_ = _⊑?_
    }
  ; unimodality = unimodality
  }

