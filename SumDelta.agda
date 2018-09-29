
open import RelationalStructures

module SumDelta {cL ℓ⊑L ℓ<L ℓ≈L cR ℓ⊑R ℓ<R ℓ≈R} 
                (deltaL : DeltaPoset {cL} {ℓ⊑L} {ℓ<L} {ℓ≈L}) 
                (deltaR : DeltaPoset {cR} {ℓ⊑R} {ℓ<R} {ℓ≈R}) where

open import Relation.Binary
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Unit
open import Function using (_$_)
open import Data.Sum.Relation.LeftOrder as LO
open import Data.Sum.Relation.Pointwise as PW

CarrierL = DeltaPoset.Carrier deltaL
CarrierR = DeltaPoset.Carrier deltaR
_L<_ = DeltaPoset._<_ deltaL
_R<_ = DeltaPoset._<_ deltaR
_L⊑_ = DeltaPoset._⊑_ deltaL
_R⊑_ = DeltaPoset._⊑_ deltaR
_L∥_ = DeltaPoset._∥_ deltaL
_R∥_ = DeltaPoset._∥_ deltaR
_L∦_ = DeltaPoset._∦_ deltaL
_R∦_ = DeltaPoset._∦_ deltaR
_L≈_ =  DeltaPoset._≈_ deltaL
_R≈_ =  DeltaPoset._≈_ deltaR
unimL = DeltaPoset.unimodality deltaL
unimR = DeltaPoset.unimodality deltaR

Carrier' = CarrierL ⊎ CarrierR
_<'_ = _L<_ ⊎-< _R<_
_⊑'_ = Pointwise _L⊑_ _R⊑_
_≈'_ = Pointwise _L≈_ _R≈_

_∦'_ : Carrier' → Carrier' → Set _
a ∦' b = (a ⊑' b) ⊎ (b ⊑' a)  

_∥'_ : Carrier' → Carrier' → Set _
a ∥' b = ¬ (a ∦' b)

tosetLR : IsStrictTotalOrder _≈'_ _<'_ 
tosetLR = ⊎-<-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder deltaL) (DeltaPoset.isStrictTotalOrder deltaR)

partialOrderLR : IsPartialOrder _≈'_ _⊑'_
partialOrderLR = ⊎-isPartialOrder (DeltaPoset.isPartialOrder deltaL) (DeltaPoset.isPartialOrder deltaR)

≈'-equiv : IsEquivalence _≈'_
≈'-equiv = IsPartialOrder.isEquivalence partialOrderLR

≈'-setoid : Setoid _ _
≈'-setoid = record
  { Carrier = Carrier'
  ; isEquivalence = ≈'-equiv
  }

unimodality : {a b c : Carrier'} → a <' b → b <' c → a ∥' b → b ∥' c → a ∥' c
unimodality {inj₁ a'} {inj₂ b'} {inj₁ c'} (₁∼₂ .tt) () a∥b b∥c a∦c
unimodality {inj₁ a'} {inj₂ b'} {inj₂ c'} (₁∼₂ .tt) (₂∼₂ b'<c') a∥b b∥c (inj₁ (₁∼₂ ()))
unimodality {inj₁ a'} {inj₂ b'} {inj₂ c'} (₁∼₂ .tt) (₂∼₂ b'<c') a∥b b∥c (inj₂ ())
unimodality {inj₁ a'} {inj₁ b'} {inj₂ c'} (₁∼₁ a'<b') (₁∼₂ .tt) a∥b b∥c (inj₁ (₁∼₂ ()))
unimodality {inj₁ a'} {inj₁ b'} {inj₂ c'} (₁∼₁ a'<b') (₁∼₂ .tt) a∥b b∥c (inj₂ ())
unimodality {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c a∦c with a'∥b' | b'∥c'
  where
    a'∥b' : a' L∥ b'
    a'∥b' (inj₁ a'⊑b') = a∥b $ inj₁ (₁∼₁ a'⊑b')
    a'∥b' (inj₂ b'⊑a') = a∥b $ inj₂ (₁∼₁ b'⊑a')

    b'∥c' : b' L∥ c'
    b'∥c' (inj₁ b'⊑c') = b∥c $ inj₁ (₁∼₁ b'⊑c')
    b'∥c' (inj₂ c'⊑b') = b∥c $ inj₂ (₁∼₁ c'⊑b')
unimodality {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c (inj₁ (₁∼₁ a'⊑c')) | a'∥b' | b'∥c' =
  (unimL a'<b' b'<c' a'∥b' b'∥c') (inj₁ a'⊑c')
unimodality {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c (inj₂ (₁∼₁ c'⊑a')) | a'∥b' | b'∥c' =
  (unimL a'<b' b'<c' a'∥b' b'∥c') (inj₂ c'⊑a')
unimodality {inj₂ a'} {inj₂ b'} {inj₂ c'} (₂∼₂ a'<b') (₂∼₂ b'<c') a∥b b∥c a∦c with a'∥b' | b'∥c'
  where
    a'∥b' : a' R∥ b'
    a'∥b' (inj₁ a'⊑b') = a∥b $ inj₁ (₂∼₂ a'⊑b')
    a'∥b' (inj₂ b'⊑a') = a∥b $ inj₂ (₂∼₂ b'⊑a')

    b'∥c' : b' R∥ c'
    b'∥c' (inj₁ b'⊑c') = b∥c $ inj₁ (₂∼₂ b'⊑c')
    b'∥c' (inj₂ c'⊑b') = b∥c $ inj₂ (₂∼₂ c'⊑b')
unimodality {inj₂ a'} {inj₂ b'} {inj₂ c'} (₂∼₂ a'<b') (₂∼₂ b'<c') a∥b b∥c (inj₁ (₂∼₂ a'⊑c')) | a'∥b' | b'∥c' =
  (unimR a'<b' b'<c' a'∥b' b'∥c') (inj₁ a'⊑c')
unimodality {inj₂ a'} {inj₂ b'} {inj₂ c'} (₂∼₂ a'<b') (₂∼₂ b'<c') a∥b b∥c (inj₂ (₂∼₂ c'⊑a')) | a'∥b' | b'∥c' =
  (unimR a'<b' b'<c' a'∥b' b'∥c') (inj₂ c'⊑a')

sumDeltaPoset : DeltaPoset {_} {_} {_} {_}
sumDeltaPoset = record  
  { Carrier = Carrier'
  ; _⊑_ = _⊑'_
  ; _<_ = _<'_
  ; isStrictTotalOrder = tosetLR
  ; isDecPartialOrder = record
    { isPartialOrder = partialOrderLR
    ; _≟_ = ⊎-decidable (DeltaPoset._≈?_ deltaL) (DeltaPoset._≈?_ deltaR) 
    ; _≤?_ = ⊎-decidable (DeltaPoset._⊑?_ deltaL) (DeltaPoset._⊑?_ deltaR) 
    }
  ; unimodality = unimodality
  }
