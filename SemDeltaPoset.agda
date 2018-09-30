
open import Function using (_$_ ; _|>′_)
open import Syntax
open import Kinding
open import BoolPoset
open import Relation.Nullary
open import Relation.Binary
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.List
open import Data.List.Any as LAny
open import Level
open import Util using (l0;l1;l2)
open import Data.Unit renaming (preorder to unitPreorder ; decTotalOrder to unitToset) hiding (_≤_)
open import Data.Nat as N hiding (_<_ ; _⊔_)
open import Data.Nat.Properties as NP
open import Data.Bool
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import FreeForgetfulAdjunction
open import RelationalStructures
open Util

module SemDeltaPoset where

discreteDelta : StrictTotalOrder l0 l0 l0 → DeltaPoset {l0} {l0} {l0} {l0}
discreteDelta sto = deltaPoset
  where 
    open import DiscreteDelta sto 

postulate
  --TODO: implement this
  ⟦_T⟧ : ∀ {τ : τ} → IsToset τ → StrictTotalOrder l0 l0 l0

-- agda-mode: ⁑ is \asterisk, second choice
⟦_⁑⟧ : ∀ {τ : τ} → IsDeltaPoset τ → DeltaPoset {l0} {l0} {l0} {l0}
⟦ UnitDelta ⁑⟧ = record
   { Carrier = ⊤ 
   ; _⊑_ = _⊑_ 
   ; _<_ = _<_
   ; isStrictTotalOrder = UnitStrictTotal.⊤-IsStrictTotalOrder
   ; isDecPartialOrder = ⊤≤-isDecPartialOrder
   ; unimodality = unimodality
   }
  where
    open import UnitPoset
    _⊑_ = _⊤≤_
    _<_ = UnitStrictTotal._⊤<_

    _∦_ : ⊤ → ⊤ → Set
    x ∦ y = x ⊤≤ y ⊎ y ⊤≤ x
    
    _∥_ : ⊤ → ⊤ → Set
    _∥_ x y = ¬ (x ∦ y)

    unimodality : {a b c : ⊤} → a < b → b < c → a ∥ b → b ∥ c → a ∥ c
    unimodality () () _ _
⟦ NatDelta ⁑⟧ = record
  { Carrier = ℕ 
  ; _⊑_ = _⊑_
  ; _<_ = _<_
  ; isStrictTotalOrder = NP.<-isStrictTotalOrder
  ; isDecPartialOrder = record
    { isPartialOrder = natPartialOrder
    ; _≟_ = IsDecEquivalence._≟_ ≡-isDecEquivalence
    ; _≤?_ = N._≤?_
    }
  ; unimodality = unimodality
  }
  where
    _⊑_ = N._≤_
    _<_ = N._<_

    _∦_ : ℕ → ℕ → Set
    x ∦ y = x ⊑ y ⊎ y ⊑ x
    
    _∥_ : ℕ → ℕ → Set
    _∥_ x y = ¬ (x ∦ y)

    natPartialOrder : IsPartialOrder _≡_ _⊑_
    natPartialOrder = 
      let tot = IsDecTotalOrder.isTotalOrder NP.≤-isDecTotalOrder
          part = IsTotalOrder.isPartialOrder tot
      in 
        part

    unimodality : {a b c : ℕ} → a < b → b < c → a ∥ b → b ∥ c → a ∥ c
    unimodality {a} {b} {c} _ _ a∥b b∥c = ⊥-elim $ a∥b (≤-total a b)

{-      
⟦ DiscreteProductDelta isTosetL isDeltaR ⁑⟧ = record
  { Carrier = |L×R|
  ; _⊑_ = _⊑_
  ; _<_ = _<_
  ; isStrictTotalOrder = <-strict
  ; isDecPartialOrder = record
    { isPartialOrder = ⊑-decPartialOrder
    ; _≟_ = ≈'-decidable
    ; _≤?_ = ⊑-decidable
    }
  ; unimodality = unimodality
  }
  where
    open import Data.Product.Relation.Lex.Strict as LS
    open import Data.Product.Relation.Pointwise.NonDependent as PW
    open import DiscreteDelta ⟦ isTosetL T⟧ renaming (unimodality to unimodalityL)

    deltaL = deltaPoset
    deltaR = ⟦ isDeltaR ⁑⟧
    |L×R| = (DeltaPoset.Carrier deltaL) × (DeltaPoset.Carrier deltaR) 
    _L<_ = DeltaPoset._<_ deltaL
    compareL = DeltaPoset.compare deltaL
    _R<_ = DeltaPoset._<_ deltaR
    compareR = DeltaPoset.compare deltaR
    _L⊑_ = DeltaPoset._⊑_  deltaL
    _R⊑_ = DeltaPoset._⊑_ deltaR    
    _L∥_ = DeltaPoset._∥_  deltaL
    _R∥_ = DeltaPoset._∥_ deltaR
    unimR = DeltaPoset.unimodality deltaR

    _≈'_ = Pointwise (DeltaPoset._≈_ deltaL) (DeltaPoset._≈_ deltaR)
    _<_ = ×-Lex (DeltaPoset._≈_ deltaL) _L<_ _R<_
    _⊑_ = Pointwise _L⊑_ _R⊑_
    
    _∦_ : Rel |L×R| _
    a ∦ b = a ⊑ b ⊎ b ⊑ a 

    _∥_ : Rel |L×R| _
    a ∥ b = ¬ (a ∦ b)

    ⊑-decPartialOrder : IsPartialOrder _≈'_ _⊑_
    ⊑-decPartialOrder = ×-isPartialOrder (DeltaPoset.isPartialOrder deltaL) (DeltaPoset.isPartialOrder deltaR)

    ≈'-decidable : Decidable _≈'_
    ≈'-decidable = PW.×-decidable (DeltaPoset._≈?_ deltaL) (DeltaPoset._≈?_ deltaR)

    ⊑-decidable : Decidable _⊑_
    ⊑-decidable = PW.×-decidable (DeltaPoset._⊑?_ deltaL) (DeltaPoset._⊑?_ deltaR)

    <-strict : IsStrictTotalOrder _≈'_ _<_
    <-strict = LS.×-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder deltaL) (DeltaPoset.isStrictTotalOrder deltaR)

    unimodality : {a b c : |L×R|} → a < b → b < c → a ∥ b → b ∥ c → a ∥ c
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₁ aL<bL) (inj₁ bL<cL) a∥b b∥c (inj₁ (⊑-refl aL≈cL , aR⊑cR)) = 
      irrefl< {aL} {cL} aL≈cL aL<cL
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.trans< deltaL {aL} {bL} {cL} aL<bL bL<cL
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₁ aL<bL) (inj₁ bL<cL) a∥b b∥c (inj₂ (⊑-refl cL≈aL , cR⊑aR)) = 
      irrefl< {aL} {cL} (sym≈ {cL} {aL} cL≈aL) aL<cL 
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.trans< deltaL {aL} {bL} {cL} aL<bL bL<cL        
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₁ aL<bL) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c (inj₁ (⊑-refl aL≈cL , aR⊑cR)) = 
      irrefl< {aL} {cL} aL≈cL aL<cL 
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.<-respʳ-≈ deltaL {aL} {bL} {cL} bL≈cL aL<bL 
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₁ aL<bL) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c (inj₂ (⊑-refl cL≈aL , aR⊑cR)) = 
      irrefl< {aL} {cL} (sym≈ {cL} {aL} cL≈aL) aL<cL 
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.<-respʳ-≈ deltaL {aL} {bL} {cL} bL≈cL aL<bL 
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) (inj₁ bL<cL) a∥b b∥c (inj₁ (⊑-refl aL≈cL , cR⊑aR)) = 
      irrefl< {aL} {cL} aL≈cL aL<cL 
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.<-respˡ-≈ deltaL {cL} {bL} {aL} (sym≈ {aL} {bL} aL≈bL) bL<cL 
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) (inj₁ bL<cL) a∥b b∥c (inj₂ (⊑-refl cL≈aL , aR⊑cR)) = 
      irrefl< {aL} {cL} (sym≈ {cL} {aL} cL≈aL) aL<cL 
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.<-respˡ-≈ deltaL {cL} {bL} {aL} (sym≈ {aL} {bL} aL≈bL) bL<cL
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c a∦c with aR∥bR | bR∥cR 
      where
        aR∥bR : aR R∥ bR
        aR∥bR (inj₁ aR⊑bR) = a∥b $ inj₁ (DeltaPoset.reflexive⊑ deltaL aL≈bL , aR⊑bR)
        aR∥bR (inj₂ bR⊑aR) = a∥b $ inj₂ (DeltaPoset.reflexive⊑ deltaL (sym≈ {aL} {bL} aL≈bL) , bR⊑aR)

        bR∥cR : bR R∥ cR
        bR∥cR (inj₁ bR⊑cR) = b∥c $ inj₁ (DeltaPoset.reflexive⊑ deltaL bL≈cL , bR⊑cR)
        bR∥cR (inj₂ cR⊑bR) = b∥c $ inj₂ (DeltaPoset.reflexive⊑ deltaL (sym≈ {bL} {cL} bL≈cL) , cR⊑bR)
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c (inj₁ (⊑-refl aL≈cL , aR⊑cR)) | aR∥bR | bR∥cR = 
      (unimR aR<bR bR<cR aR∥bR bR∥cR) (inj₁ aR⊑cR)
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c (inj₂ (⊑-refl cL≈aL , cR⊑aR)) | aR∥bR | bR∥cR = 
      (unimR aR<bR bR<cR aR∥bR bR∥cR) (inj₂ cR⊑aR)
-}
⟦ SumDelta isDeltaL isDeltaR ⁑⟧ = sumDeltaPoset
  where 
    open import SumDelta ⟦ isDeltaL ⁑⟧ ⟦ isDeltaR ⁑⟧
{-
⟦ DiscreteDelta isTosetContents ⁑⟧ = discreteDelta ⟦ isTosetContents T⟧ 

⟦ PartialDelta isDeltaContents ⁑⟧ = record  
  { Carrier = |Cᵀ|
  ; _⊑_ = _⊑ᵀ_
  ; _<_ = _<ᵀ_
  ; isStrictTotalOrder = <ᵀ-strict
  ; isDecPartialOrder = record
    { isPartialOrder = ⊑ᵀ-partial
    ; _≟_ = ⊎-decidable (DeltaPoset._≈?_ deltaContents) (UnitPoset._⊤≟_)
    ; _≤?_ = ⊎-<-decidable (DeltaPoset._⊑?_ deltaContents) (IsDecPartialOrder._≤?_ ⊤≤-isDecPartialOrder) dec-aux
    }
  ; unimodality = unimodality
  }
  where
    open import UnitPoset
    open UnitStrictTotal
    open import Data.Sum.Relation.LeftOrder as LO
    open import Data.Sum.Relation.Pointwise as PW
    open import Function 

    deltaContents = ⟦ isDeltaContents ⁑⟧ 
    |C| = DeltaPoset.Carrier deltaContents
    _<₀_ = DeltaPoset._<_ deltaContents
    _⊑₀_ = DeltaPoset._⊑_ deltaContents
    _≈₀_ = Pointwise (DeltaPoset._≈_ deltaContents) (_≡_ {A = ⊤})
    _∥₀_ = DeltaPoset._∥_ deltaContents
    _∦₀_ = DeltaPoset._∦_ deltaContents
    unim₀ = DeltaPoset.unimodality deltaContents

    dec-aux : ∀ {x y} → Dec (inj₁ x ⟨ _⊑₀_ ⊎-< _⊤≤_ ⟩ inj₂ y)
    dec-aux {x} {y} = yes (₁∼₂ tt)

    -- -ᵀ Carrier
    |Cᵀ| : Set
    |Cᵀ| = |C| ⊎ ⊤

    _<ᵀ_ : |Cᵀ| → |Cᵀ| → Set
    _<ᵀ_ = (_<₀_) ⊎-< (UnitStrictTotal._⊤<_)

    <ᵀ-strict = ⊎-<-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder deltaContents) ⊤-IsStrictTotalOrder

    _⊑ᵀ_ : |Cᵀ| → |Cᵀ| → Set
    _⊑ᵀ_ = (_⊑₀_) ⊎-< (_⊤≤_)  

    _∦ᵀ_ : |Cᵀ| → |Cᵀ| → Set
    a ∦ᵀ b = (a ⊑ᵀ b) ⊎ (b ⊑ᵀ a)  

    _∥ᵀ_ : |Cᵀ| → |Cᵀ| → Set
    a ∥ᵀ b = ¬ (a ∦ᵀ b)
 
    ⊑ᵀ-partial = 
      ⊎-<-isPartialOrder
        (DeltaPoset.isPartialOrder deltaContents) 
        (IsDecPartialOrder.isPartialOrder ⊤≤-isDecPartialOrder)

    unimodality : {a b c : |Cᵀ|} → a <ᵀ b → b <ᵀ c → a ∥ᵀ b → b ∥ᵀ c → a ∥ᵀ c
    unimodality {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c a∦c with a'∥c'        
      where
        a'∥b' : a' ∥₀ b'
        a'∥b' (inj₁ a'⊑b') = a∥b $ inj₁ (₁∼₁ a'⊑b') 
        a'∥b' (inj₂ b'⊑a') = a∥b $ inj₂ (₁∼₁ b'⊑a')

        b'∥c' : b' ∥₀ c'
        b'∥c' (inj₁ b'⊑c') = b∥c $ inj₁ (₁∼₁ b'⊑c') 
        b'∥c' (inj₂ c'⊑b') = b∥c $ inj₂ (₁∼₁ c'⊑b')

        a'∥c' : a' ∥₀ c'
        a'∥c' = unim₀ a'<b' b'<c' a'∥b' b'∥c' 
    unimodality {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c (inj₁ (₁∼₁ a'⊑c')) | a'∥c' = 
       a'∥c' (inj₁ a'⊑c') 
    unimodality {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ b'<c') (₁∼₁ x∼₁y) a∥b b∥c (inj₂ (₁∼₁ c'⊑a')) | a'∥c' = 
      a'∥c' (inj₂ c'⊑a')
    unimodality {inj₁ a'} {inj₁ b'} {inj₂ .tt} a<b b<c a∥b b∥c a∦c = 
      b∥c $ inj₁ (₁∼₂ tt)
    unimodality {inj₁ a'} {inj₂ .tt} {inj₁ c'} a<b () a∥b b∥c
    unimodality {inj₁ a'} {inj₂ .tt} {inj₂ .tt} a<b (₂∼₂ ()) a∥b b∥c
    unimodality {inj₂ .tt} {inj₁ b'} {c} () b<c a∥b b∥c
    unimodality {inj₂ .tt} {inj₂ .tt} {c} (₂∼₂ ()) b<c a∥b b∥c
-}
