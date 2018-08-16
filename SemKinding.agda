module SemKinding where

open import Function using (_$_)
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

open Preorder

-- agda-mode: ⁎ is \asterisk, first choice
⟦_⁎⟧ : ∀ {τ : τ} → IsPoset τ → Preorder0
⟦ FunPoset {q = q} domIsProset codIsProset ⁎⟧ = 
  record{ 
    Carrier = D⇒C ;
    _≈_ = _≡_ ;
    _∼_ = _leq_ ;
    isPreorder = leqPreorder 
   }  
  where
    domProset : Preorder0
    domProset = ⟦ domIsProset ⁎⟧ 
    
    codProset : Preorder0
    codProset = ⟦ codIsProset ⁎⟧

    D : Set
    D = Carrier domProset
    _d≈_ : D → D → Set
    _d≈_ = _≈_ domProset
    _d≤_ : D → D → Set
    _d≤_ = _∼_ domProset
    
    C : Set
    C = Carrier codProset
    _c≈_ : C → C → Set
    _c≈_ = _≈_ codProset
    _c≤_ : C → C → Set
    _c≤_ = _∼_ codProset
    isPreorderCod : IsPreorder _c≈_ _c≤_
    isPreorderCod = isPreorder codProset
    
    D⇒C : Set
    D⇒C = Σ[ f ∈ (D → C) ] (∀{v₁ v₂ : D} → v₁ d≤ v₂ → (f v₁) c≤ (f v₂))
    
    _leq_ : D⇒C → D⇒C → Set
    (f , _) leq (g , _) = ∀{v : D} → (f v) c≤ (g v) 
    
    isRefl : _≡_ ⇒ _leq_
    isRefl {(f , _)} PE.refl {v} = reflexiveCod fv≈fv
      where
        reflexiveCod : _c≈_ ⇒ _c≤_
        reflexiveCod = IsPreorder.reflexive isPreorderCod
        
        isEq≈ : IsEquivalence _c≈_ 
        isEq≈ = IsPreorder.isEquivalence isPreorderCod
        
        fv≈fv : (f v) c≈ (f v)
        fv≈fv = IsEquivalence.refl isEq≈ {f v}

    leqTransitive : Transitive _leq_
    leqTransitive {(f , _)} {(g , _)} {(h , _)} f≤g g≤h {v} = trans≤ fv≤gv gv≤hv 
      where
        fv≤gv : (f v) c≤ (g v)
        fv≤gv = f≤g {v}

        gv≤hv : (g v) c≤ (h v)
        gv≤hv = g≤h {v}

        trans≤ : Transitive _c≤_
        trans≤ = IsPreorder.trans isPreorderCod
        
    leqPreorder : IsPreorder _≡_ _leq_
    leqPreorder = 
      record{
         isEquivalence = PE.isEquivalence ;
         reflexive =  isRefl ;
         trans = (λ {i} → λ {j} → λ {k} → leqTransitive {i} {j} {k}) 
       }

⟦ UnitPoset ⁎⟧ = unitPreorder
⟦ BoolPoset ⁎⟧ = B≤-preorder
⟦ NatPoset ⁎⟧ = NP.≤-preorder

⟦_T⟧ : ∀ {τ : τ} → IsToset τ → StrictTotalOrder l0 l0 l0
⟦ x T⟧ = {!!}   

discreteDelta : StrictTotalOrder l0 l0 l0 → DeltaPoset {l0} {l0} {l0} {l0}
discreteDelta sto = deltaPoset
  where 
    open import DiscreteDelta sto 
  
{-
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
  where
    |C| = StrictTotalOrder.Carrier sto
    _≈₀_ = StrictTotalOrder._≈_ sto
    ≈-setoid = StrictTotalOrder.decSetoid sto
    _≟₀_ = StrictTotalOrder._≟_ sto
    _<₀_ = StrictTotalOrder._<_ sto
    irrefl< = StrictTotalOrder.irrefl sto
    trans< = StrictTotalOrder.trans sto
    sym≈ = DecSetoid.sym ≈-setoid

    data _⊑₀_ : |C| → |C| → Set where
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

    _∦₀_ : |C| → |C| → Set
    a ∦₀ b = a ⊑₀ b ⊎ b ⊑₀ a

    _∥₀_ : |C| → |C| → Set
    a ∥₀ b = ¬ (a ∦₀ b)

    unimodality : {a b c : |C|} → a <₀ b → b <₀ c → a ∥₀ b → b ∥₀ c → a ∥₀ c
    unimodality a<b b<c a∥b b∥c (inj₁ (⊑-refl a≈c)) = irrefl< a≈c (trans< a<b b<c)
    unimodality a<b b<c a∥b b∥c (inj₂ (⊑-refl c≈a)) = irrefl< (sym≈ c≈a) (trans< a<b b<c)
-}

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
      irrefl< {aL} {cL} aL<cL aL≈cL
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.trans< deltaL {aL} {bL} {cL} aL<bL bL<cL
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₁ aL<bL) (inj₁ bL<cL) a∥b b∥c (inj₂ (⊑-refl cL≈aL , cR⊑aR)) = 
      irrefl< {aL} {cL} aL<cL (sym≈ {cL} {aL} cL≈aL)
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.trans< deltaL {aL} {bL} {cL} aL<bL bL<cL        
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₁ aL<bL) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c (inj₁ (⊑-refl aL≈cL , aR⊑cR)) = 
      irrefl< {aL} {cL} aL<cL aL≈cL
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.<-respʳ-≈ deltaL {aL} {bL} {cL} bL≈cL aL<bL 
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₁ aL<bL) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c (inj₂ (⊑-refl cL≈aL , aR⊑cR)) = 
      irrefl< {aL} {cL} aL<cL (sym≈ {cL} {aL} cL≈aL)
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.<-respʳ-≈ deltaL {aL} {bL} {cL} bL≈cL aL<bL 
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) (inj₁ bL<cL) a∥b b∥c (inj₁ (⊑-refl aL≈cL , cR⊑aR)) = 
      irrefl< {aL} {cL} aL<cL aL≈cL
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.<-respˡ-≈ deltaL {cL} {bL} {aL} (sym≈ {aL} {bL} aL≈bL) bL<cL 
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) (inj₁ bL<cL) a∥b b∥c (inj₂ (⊑-refl cL≈aL , aR⊑cR)) = 
      irrefl< {aL} {cL} aL<cL (sym≈ {cL} {aL} cL≈aL)
      where
        aL<cL : aL L< cL
        aL<cL = DeltaPoset.<-respˡ-≈ deltaL {cL} {bL} {aL} (sym≈ {aL} {bL} aL≈bL) bL<cL
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c a∦c with aR∥bR | bR∥cR 
      where
        aR∥bR : aR R∥ bR
        aR∥bR (inj₁ aR⊑bR) = a∥b $ inj₁ (DeltaPoset.refl⊑ deltaL aL≈bL , aR⊑bR)
        aR∥bR (inj₂ bR⊑aR) = a∥b $ inj₂ (DeltaPoset.refl⊑ deltaL (sym≈ {aL} {bL} aL≈bL) , bR⊑aR)

        bR∥cR : bR R∥ cR
        bR∥cR (inj₁ bR⊑cR) = b∥c $ inj₁ (DeltaPoset.refl⊑ deltaL bL≈cL , bR⊑cR)
        bR∥cR (inj₂ cR⊑bR) = b∥c $ inj₂ (DeltaPoset.refl⊑ deltaL (sym≈ {bL} {cL} bL≈cL) , cR⊑bR)
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c (inj₁ (⊑-refl aL≈cL , aR⊑cR)) | aR∥bR | bR∥cR = 
      (unimR aR<bR bR<cR aR∥bR bR∥cR) (inj₁ aR⊑cR)
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c (inj₂ (⊑-refl cL≈aL , cR⊑aR)) | aR∥bR | bR∥cR = 
      (unimR aR<bR bR<cR aR∥bR bR∥cR) (inj₂ cR⊑aR)

⟦ SumDelta isDeltaL isDeltaR ⁑⟧ = record  
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
  where 
    open import Data.Sum.Relation.LeftOrder as LO
    open import Data.Sum.Relation.Pointwise as PW

    deltaL = ⟦ isDeltaL ⁑⟧
    deltaR = ⟦ isDeltaR ⁑⟧
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

    _∦'_ : Carrier' → Carrier' → Set
    a ∦' b = (a ⊑' b) ⊎ (b ⊑' a)  

    _∥'_ : Carrier' → Carrier' → Set
    a ∥' b = ¬ (a ∦' b)
 
    tosetLR : IsStrictTotalOrder _≈'_ _<'_ 
    tosetLR = ⊎-<-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder deltaL) (DeltaPoset.isStrictTotalOrder deltaR)

    partialOrderLR : IsPartialOrder _≈'_ _⊑'_
    partialOrderLR = ⊎-isPartialOrder (DeltaPoset.isPartialOrder deltaL) (DeltaPoset.isPartialOrder deltaR)

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

open import Relation.Binary.Lattice
open import Function.Inverse

record SemSemilat (cₛ ℓₛ₁ ℓₛ₂ cₚ ℓ⊑ₚ ℓ<ₚ ℓ~ₚ : Level) {τ τ₀ : τ} (isSemilat : IsSemilat τ τ₀)
                   : Set (Level.suc $ cₛ ⊔ ℓₛ₁ ⊔ ℓₛ₂ ⊔ cₚ ⊔ ℓ⊑ₚ ⊔ ℓ<ₚ ⊔ ℓ~ₚ) where
  field
    -- direct representation of semilattice
    S : BoundedJoinSemilattice cₛ ℓₛ₁ ℓₛ₂
    -- delta poset (freely generates S up-to-isomorphism)
    P : DeltaPoset {cₚ} {ℓ⊑ₚ} {ℓ<ₚ} {ℓ~ₚ}
    -- injection of τ₀ deltaPoset interpretation into P
    i : P ↣+ ⟦ delta-isToset isSemilat ⁑⟧ 
    -- factorization into free semilattice
    f : S ⇉ FP P
    -- defactorization out of free semilattice
    g : FP P ⇉ S
    -- f and g are inverses
    inv-S→FP→S : (a : BoundedJoinSemilattice.Carrier S) → (BoundedJoinSemilattice._≈_ S (proj₁ g $ proj₁ f $ a) a) 
    inv-FP→S→FP : (a : BoundedJoinSemilattice.Carrier $ FP P) → (BoundedJoinSemilattice._≈_ (FP P) (proj₁ f $ proj₁ g $ a) a) 

⟦_⁂⟧ : ∀ {τ τ₀ : τ} → (isSemilat : IsSemilat τ τ₀) → SemSemilat l0 l0 l0 l0 l0 l0 l0 isSemilat       
{-      
⟦_⁂⟧ NatSemilat = record
  { S = S
  ; P = P
  ; i = i
  ; f = |f| , |f|-⊥ , |f|-∨
  ; g = |g| , |g|-⊥ , |g|-∨
  ; inv-S→FP→S = inv-S→FP→S
  ; inv-FP→S→FP = inv-FP→S→FP 
  }
  where
    open import Data.Nat.Base as NB renaming (_⊔_ to _N⊔_)

    least : ∀ {m n : ℕ} → (z : ℕ) → (m ≤ z) → (n ≤ z) → (m N⊔ n ≤ z) 
    least {.0} {n} z z≤n n≤z = n≤z
    least {.(N.suc _)} {.0} .(N.suc _) (s≤s pm≤pz) z≤n = s≤s pm≤pz
    least {.(N.suc _)} {.(N.suc _)} .(N.suc _) (s≤s pm≤pz) (s≤s pn≤pz) = 
      let
        pm⊔pn≤pz = least _ pm≤pz pn≤pz 
      in 
        s≤s pm⊔pn≤pz
 
    S : BoundedJoinSemilattice l0 l0 l0
    S = record 
      { Carrier = ℕ
      ; _≈_ = _≡_
      ; _≤_ = N._≤_
      ; _∨_ = NB._⊔_
      ; ⊥ = N.zero
      ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
          { isPartialOrder = ≤-isPartialOrder
          ; supremum = λ x → λ y → (m≤m⊔n x y) , (n≤m⊔n x y) , least {x} {y}
          }
        ; minimum = λ n → N.z≤n {n} 
        } 
      }

    P : DeltaPoset {l0} {l0} {l0} {l0} 
    P = record
      { Carrier = Σ[ n ∈ ℕ ] ¬ (n ≡ 0)
      ; _⊑_ = _⊑₀_
      ; _<_ = _<₀_
      ; _≈_ = _≈₀_
      ; isStrictTotalOrder = isStrictTotalOrder₀
      ; isDecPartialOrder = isDecPartialOrder₀
      ; unimodality = λ {a} → λ {b} → λ {c} → unimodality {a} {b} {c}
      }
      where
        deltaPosetℕ = ⟦ NatDelta ⁑⟧ 
        
        C = Σ[ n ∈ ℕ ] ¬ (n ≡ 0)
        
        _⊑₀_ : C → C → Set _
        (n1 , p1) ⊑₀ (n2 , p2) = n1 N.≤ n2

        _<₀_ : C → C → Set _
        (n1 , p1) <₀ (n2 , p2) = n1 N.< n2

        _≈₀_ : C → C → Set _
        (n1 , p1) ≈₀ (n2 , p2) = n1 ≡ n2

        _∦₀_ : C → C → Set
        a ∦₀ b = a ⊑₀ b ⊎ b ⊑₀ a

        _∥₀_ : C → C → Set
        a ∥₀ b = ¬ (a ∦₀ b)
        
        unimodality : {a b c : C} → (a <₀ b) → (b <₀ c) → (a ∥₀ b) → (b ∥₀ c) → (a ∥₀ c)
        unimodality = DeltaPoset.unimodality ⟦ NatDelta ⁑⟧ 

        <₀-compare : Trichotomous _≈₀_ _<₀_
        <₀-compare (a , _) (b , _) = <-cmp a b

        ⊑₀-reflexive : _≈₀_ ⇒ _⊑₀_
        ⊑₀-reflexive {a , _} {b , _} a≈b = ≤-reflexive {a} {b} a≈b

        isEquiv₀ : IsEquivalence _≈₀_
        isEquiv₀ = record
          { refl = PE.refl
          ; sym = PE.sym
          ; trans = PE.trans
          }

        _≟₀_ : Decidable _≈₀_
        (a , _) ≟₀ (b , _) = a N.≟ b

        _⊑₀?_ : Decidable _⊑₀_
        (a , _) ⊑₀? (b , _) = a N.≤? b

        isStrictTotalOrder₀ : IsStrictTotalOrder _≈₀_ _<₀_
        isStrictTotalOrder₀ = record
          { isEquivalence = isEquiv₀
          ; trans = <-trans
          ; compare = <₀-compare
          }

        isDecPartialOrder₀ : IsDecPartialOrder _≈₀_ _⊑₀_
        isDecPartialOrder₀ = record
          { isPartialOrder = record
            { isPreorder = record
                { isEquivalence = isEquiv₀
                ; reflexive = λ {a} → λ {b} → ⊑₀-reflexive {a} {b}
                ; trans = ≤-trans
                }
            ; antisym = ≤-antisym
            }
          ; _≟_ = _≟₀_
          ; _≤?_ = _⊑₀?_
          }

    |i| : (DeltaPoset.Carrier P) → (DeltaPoset.Carrier ⟦ NatDelta ⁑⟧)
    |i| (n , p) = n

    |i|-monotone : monotone P ⟦ NatDelta ⁑⟧ |i|
    |i|-monotone {n , _} {n' , _} n⊑n' = n⊑n'
      
    |i|-monic : monic (DeltaPoset.≈-setoid P) (DeltaPoset.≈-setoid ⟦ NatDelta ⁑⟧) |i|
    |i|-monic {a , _} {a' , _} fa≈fa' = fa≈fa' 

    i : P ↣+ ⟦ NatDelta ⁑⟧
    i = (|i| , (λ {a} → λ {a'} → |i|-monotone {a} {a'}) , (λ {a} → λ {a'} → |i|-monic {a} {a'}))

    open DeltaPoset P
    open import Data.List.Relation.Pointwise as PW
    open import FreeSemilattice P renaming (SemilatCarrier to FP-Carrier ; ⊥ to ⊥ₚ ; _≈_ to _≈ₚ_ ; _∨_ to _∨ₚ_ ; ∷-Free to ∷-Free)

    |f| : ℕ → FP-Carrier 
    |f| zero = [] , []-Free 
    |f| n@(suc n') = [ (n , (λ ())) ] , sng-free

    |f|-⊥ : |f| 0 ≈ₚ ⊥ₚ
    |f|-⊥ = []

    |f|-∨ : (n0 n1 : ℕ) → |f| (n0 N.⊔ n1) ≈ₚ (|f| n0 ∨ₚ |f| n1)
    |f|-∨ N.zero N.zero = []
    |f|-∨ N.zero (N.suc n1) = PE.refl ∷ [] 
    |f|-∨ (N.suc n0') N.zero = PE.refl ∷ []
    |f|-∨ (N.suc n0') (N.suc n1') with n0' N.≤? n1' | n1' N.≤? n0'
    |f|-∨ (N.suc n0') (N.suc n1') | yes n0'≤n1' | yes n1'≤n0' with NP.≤-antisym n0'≤n1' n1'≤n0'
    |f|-∨ (N.suc n0') (N.suc n1') | yes n0'≤n1' | yes n1'≤n0' | PE.refl rewrite NP.⊔-idem n0' = PE.refl ∷ []
    |f|-∨ (N.suc n0') (N.suc n1') | yes n0'≤n1' | no ¬n1'≤n0' rewrite m≤n⇒m⊔n≡n n0'≤n1' = PE.refl ∷ []
    |f|-∨ (N.suc n0') (N.suc n1') | no ¬n0'≤n1' | yes n1'≤n0' rewrite m≤n⇒n⊔m≡n n1'≤n0' = PE.refl ∷ []
    |f|-∨ (N.suc n0') (N.suc n1') | no ¬n0'≤n1' | no ¬n1'≤n0' with ≤-total n0' n1'
    |f|-∨ (N.suc n0') (N.suc n1') | no ¬n0'≤n1' | no ¬n1'≤n0' | inj₁ n0'≤n1' = ⊥-elim $ ¬n0'≤n1' n0'≤n1'
    |f|-∨ (N.suc n0') (N.suc n1') | no ¬n0'≤n1' | no ¬n1'≤n0' | inj₂ n1'≤n0' = ⊥-elim $ ¬n1'≤n0' n1'≤n0' 

    |g| : FP-Carrier → ℕ 
    |g| ([] , _) = 0
    |g| ((n , _) ∷ [] , _) = n
    |g| ((n , _) ∷ (m , _) ∷ _ , ∷-Free _ _ _ incomp _) = ⊥-elim $ incomp (here $ ≤-total n m)

    |g|-⊥ : |g| ⊥ₚ ≡ 0
    |g|-⊥ = PE.refl

    |g|-∨ : (s1 s2 : FP-Carrier) → |g| (s1 ∨ₚ s2) ≡ (|g| s1) N.⊔ (|g| s2)
    |g|-∨ ([] , f1) ([] , f2) = PE.refl
    |g|-∨ ([] , f1) (h2 ∷ t2 , f2) = PE.refl
    |g|-∨ c1@(h1 ∷ [] , f1) ([] , f2) rewrite ⊔-identityʳ (|g| c1) = PE.refl
    |g|-∨ (h1 ∷ [] , ∷-Free _ _ _ _ _) (h2 ∷ [] , ∷-Free _ _ _ _ _) with h1 ∦? h2
    |g|-∨ (h1 ∷ [] , ∷-Free _ _ _ _ _) (h2 ∷ [] , ∷-Free _ _ _ _ _) | l⊑r h1⊑h2 ¬h2⊑h1 = 
      PE.sym $ m≤n⇒m⊔n≡n h1⊑h2
    |g|-∨ (h1 ∷ [] , ∷-Free _ _ _ _ _) (h2 ∷ [] , ∷-Free _ _ _ _ _) | r⊑l ¬h1⊑h2 h2⊑h1 = 
      PE.sym $ m≤n⇒n⊔m≡n h2⊑h1
    |g|-∨ (h1 ∷ [] , ∷-Free _ _ _ _ _) (h2 ∷ [] , ∷-Free _ _ _ _ _) | l≈r h1≈h2 = 
      PE.sym $ m≤n⇒m⊔n≡n (refl⊑ {h1} {h2} h1≈h2)
    |g|-∨ ((h1 , _) ∷ [] , ∷-Free _ _ _ _ _) ((h2 , _) ∷ [] , ∷-Free _ _ _ _ _) | l∥r h1∥h2 = 
      ⊥-elim $ h1∥h2 (NP.≤-total h1 h2)
    |g|-∨ ((h11 , _) ∷ (h12 , _) ∷ _ , ∷-Free _ _ _ incomp _) (_ , _) =
      ⊥-elim $ incomp (here $ ≤-total h11 h12)
    |g|-∨ (_ , _) ((h21 , _) ∷ (h22 , _) ∷ _ , ∷-Free _ _ _ incomp _) =
      ⊥-elim $ incomp (here $ ≤-total h21 h22)

    inv-S→FP→S : (a : ℕ) → (|g| $ |f| a) ≡ a
    inv-S→FP→S N.zero = PE.refl
    inv-S→FP→S (N.suc a') = PE.refl

    |FP| : Set
    |FP| = BoundedJoinSemilattice.Carrier (FP P)
    
    _≈FP_ : |FP| → |FP| → Set
    _≈FP_ = BoundedJoinSemilattice._≈_ (FP P)

    inv-FP→S→FP : (a : BoundedJoinSemilattice.Carrier (FP P)) → (|f| $ |g| a) ≈FP a  
    inv-FP→S→FP a@([] , _) = PW.refl (λ {a} → PE.refl)
    inv-FP→S→FP ((N.zero , ¬h≡0) ∷ [] , _) = ⊥-elim $ ¬h≡0 PE.refl
    inv-FP→S→FP ((N.suc h , ¬h≡0) ∷ [] , _) = PE.refl ∷ []
    inv-FP→S→FP ((a , ¬a≡0) ∷ (b , ¬b≡0) ∷ _ , ∷-Free _ _ _ incomp _) = 
      ⊥-elim $ incomp (here $ NP.≤-total a b) 
  
⟦ BoolSemilat ⁂⟧ = record
  { S = S
  ; P = P
  ; i = |i| , |i|-monotone , |i|-monic
  ; f = |f| , |f|-⊥ , |f|-∨
  ; g = |g| , |g|-⊥ , |g|-∨
  ; inv-S→FP→S = inv-S→FP→S
  ; inv-FP→S→FP = inv-FP→S→FP 
  }
  where
    open import Data.Bool
    open import BoolPoset
    open import FinPoset
    open import Relation.Binary.Closure.ReflexiveTransitive
    open UnitStrictTotal
    open import UnitPoset

    lowerˡ : ∀ (a b : Bool) → a B≤ a B∨ b
    lowerˡ false false = ε
    lowerˡ false true = (here $ PE.refl , PE.refl) ◅ ε
    lowerˡ true false = ε
    lowerˡ true true = ε

    lowerʳ : ∀ (a b : Bool) → b B≤ a B∨ b
    lowerʳ false false = ε
    lowerʳ false true = ε
    lowerʳ true false = (here $ PE.refl , PE.refl) ◅ ε
    lowerʳ true true = ε
    
    least : ∀ (a b : Bool) → (z : Bool) → (a B≤ z) → (b B≤ z) → (a B∨ b B≤ z) 
    least false false false a≤z b≤z = ε
    least false false true a≤z b≤z = (here $ PE.refl , PE.refl) ◅ ε
    least false true false a≤z (here () ◅ _)
    least false true false a≤z (there () ◅ _)
    least false true true a≤z b≤z = ε
    least true false false (here () ◅ _) b≤z
    least true false false (there () ◅ _) b≤z
    least true false true a≤z b≤z = ε
    least true true false (here () ◅ _) b≤z
    least true true false (there () ◅ _) b≤z
    least true true true a≤z b≤z = ε

    minimum : Minimum _B≤_ false
    minimum false = ε
    minimum true = (here $ PE.refl , PE.refl) ◅ ε

    S : BoundedJoinSemilattice l0 l0 l0
    S = record 
      { Carrier = Bool
      ; _≈_ = _≡_
      ; _≤_ = _B≤_
      ; _∨_ = _B∨_ 
      ; ⊥ = false
      ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
          { isPartialOrder = B≤-isPartialOrder
          ; supremum =  λ x → λ y → lowerˡ x y , lowerʳ x y , least x y
          }
        ; minimum = minimum 
        } 
      }

    P : DeltaPoset {l0} {l0} {l0} {l0}
    P = ⟦ UnitDelta ⁑⟧ 

    |i| : (DeltaPoset.Carrier P) → (DeltaPoset.Carrier ⟦ UnitDelta ⁑⟧)
    |i| tt = tt

    |i|-monotone : monotone P ⟦ UnitDelta ⁑⟧ |i|
    |i|-monotone {tt} {tt} tt⊑tt = ε
      
    |i|-monic : monic (DeltaPoset.≈-setoid P) (DeltaPoset.≈-setoid ⟦ UnitDelta ⁑⟧) |i|
    |i|-monic {tt} {tt} _ = PE.refl 

    open DeltaPoset P
    open import Data.List.Relation.Pointwise as PW
    open import FreeSemilattice P renaming (⊥ to F⊥ ; _∨_ to _F∨_ ; _≈_ to _F≈_ )
    open import Data.List.Any.Properties
    open import Data.List.All

    |f| : Bool → Σ[ l ∈ List ⊤ ] (IsFreeList l)
    |f| false = [] , []-Free
    |f| true = tt ∷ [] , (∷-Free tt [] [] ¬Any[] []-Free) 
    
    |f|-⊥ : |f| false F≈ F⊥ 
    |f|-⊥ = PW.refl PE.refl

    |f|-∨ : (a b : Bool) → |f| (a B∨ b) F≈ (|f| a F∨ |f| b)
    |f|-∨ false false = PW.refl PE.refl
    |f|-∨ false true = PW.refl PE.refl
    |f|-∨ true false = PW.refl PE.refl
    |f|-∨ true true = PW.refl PE.refl

    |g| : Σ[ l ∈ List ⊤ ] (IsFreeList l) → Bool
    |g| ([] , []-Free) = false
    |g| (tt ∷ [] , ∷-Free _ _ _ _ _) = true
    |g| (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) = 
      ⊥-elim $ incomp (here (inj₁ $ DeltaPoset.reflexive P PE.refl))

    |g|-⊥ : |g| F⊥ ≡ false 
    |g|-⊥ = PE.refl

    |g|-∨ : (a b : Σ[ l ∈ List ⊤ ] IsFreeList l) → (|g| (a F∨ b) ≡ (|g| a) B∨ (|g| b))
    |g|-∨ ([] , []-Free) ([] , []-Free) = PE.refl
    |g|-∨ (tt ∷ [] , ∷-Free _ _ _ _ _) ([] , []-Free) = PE.refl 
    |g|-∨ ([] , []-Free) (tt ∷ [] , ∷-Free _ _ _ _ _) = PE.refl
    |g|-∨ (tt ∷ [] , ∷-Free _ _ _ _ _) (tt ∷ [] , ∷-Free _ _ _ _ _) = PE.refl
    |g|-∨ (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) _ = ⊥-elim $ incomp $ here (inj₁ $ DeltaPoset.reflexive P PE.refl) 
    |g|-∨ _ (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) = ⊥-elim $ incomp $ here (inj₁ $ DeltaPoset.reflexive P PE.refl)

    inv-S→FP→S : (a : Bool) → (|g| $ |f| a) ≡ a
    inv-S→FP→S true = PE.refl
    inv-S→FP→S false = PE.refl

    inv-FP→S→FP : (a : Σ[ l ∈ List ⊤ ] IsFreeList l) → (|f| $ |g| a) F≈ a 
    inv-FP→S→FP ([] , []-Free) = PW.refl PE.refl
    inv-FP→S→FP (tt ∷ [] , ∷-Free _ _ _ _ _) = PW.refl PE.refl
    inv-FP→S→FP (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) = ⊥-elim $ incomp $ here (inj₁ $ DeltaPoset.reflexive P PE.refl)

⟦ DictSemilat domIsToset codIsSemilat ⁂⟧ = record
  { S = {!!}
  ; P = {!!}
  ; i = {!!} , {!!} , {!!}
  ; f = {!!} , {!!} , {!!}
  ; g = {!!} , {!!} , {!!}
  ; inv-S→FP→S = {!!}
  ; inv-FP→S→FP = {!!} 
  }
  where
    open import Data.List.Relation.Pointwise as LPW
    open import Data.Product.Relation.Pointwise.NonDependent as PPW
    open import Data.List.All as LAll
    open import Data.List.Any as LAny
    open import Data.Product
 
    tosetDom = ⟦ domIsToset T⟧
    semSemilatCod = ⟦ codIsSemilat ⁂⟧
    bjsCod = SemSemilat.S semSemilatCod
    |D| = StrictTotalOrder.Carrier tosetDom
    |C| = BoundedJoinSemilattice.Carrier (SemSemilat.S semSemilatCod)

    open StrictTotalOrder tosetDom renaming (_≈_ to _≈d_ ; _<_ to _<d_ ; compare to compare-d)
    open BoundedJoinSemilattice bjsCod renaming (_≈_ to _≈c_ ; _≤_ to _≤c_ ; ⊥ to ⊥c )

    Elem : Set
    Elem = Σ[ d↦c ∈ |D| × |C| ] ¬ ((proj₂ d↦c) ≈c ⊥c) 

    _≈Elem_ : Elem → Elem → Set
    ((d1 , c1) , _) ≈Elem ((d2 , c2) , _) = (d1 ≈d d2) × (c1 ≈c c2) 

    data Sorted : List Elem → Set where
      []-Sorted : Sorted []
      ∷-Sorted : {h : Elem} → (t : List Elem) → 
                  (min : All {A = Elem} (λ e → ((proj₁ $ proj₁ h) <d (proj₁ $ proj₁ e))) t) →
                  (s : Sorted t) → Sorted (h ∷ t)

    Carrier' : Set
    Carrier' = Σ[ l ∈ List Elem ] (Sorted l)
    
    _≈'_ : Carrier' → Carrier' → Set
    (l1 , _) ≈' (l2 , _) =  LPW.Pointwise _≈Elem_ l1 l2  

    infix 4 _≤'_ 

    {-
    data _≤'_ : Carrier' → Carrier' → Set where
      ≤'-[] : [] ≤' []
      ≤'-skip : (d1 d2 : |D|) → (c1 c2 : |C|) → (t1 t2 : Carrier') → (d2 < d1) → 
                ((d1 , c1) ∷ t1 ≤' t2) → ((d1 , c1) ∷ t1 ≤' (d2 , c2) ∷ t2)
      ≤'-cmp : (d1 d2 : |D|) → (c1 c2 : |C|) → (t1 t2 : Carrier') → (d1 ≈ d2) → 
    -}

    _≤'_ : Carrier' → Carrier' → Set
    (l1 , _) ≤' (l2 , _)  = All (λ x → (Any (f x) l2)) l1
      where
        f : Elem → Elem → Set
        f ((d1 , c1) , _) ((d2 , c2) , _) = (d1 ≈d d2) × (c1 ≤c c2)

    _∨'_ : Carrier' → Carrier' → Carrier'
    ([] , _) ∨' ([] , _) = [] , []-Sorted
    ([] , _) ∨' ((h2 ∷ t2) , ∷-Sorted t2 min2 st2) = (h2 ∷ t2) , ∷-Sorted t2 min2 st2
    (h1 ∷ t1 , ∷-Sorted t1 min1 st1) ∨' ([] , []-Sorted) = h1 ∷ t1 , ∷-Sorted t1 min1 st1
    (((d1 , c1) , _) ∷ t1 , ∷-Sorted t1 min1 st1) ∨' (((d2 , c2) , _) ∷ t2 , ∷-Sorted t2 min2 st2) with compare-d d1 d2 
    (((d1 , c1) , _) ∷ t1 , ∷-Sorted t1 min1 st1) ∨' b@(((d2 , c2) , _) ∷ t2 , ∷-Sorted t2 min2 st2) | tri< d1<d2 _ _ =
      let 
        rec : Carrier'
        rec = (t1 , st1) ∨' b
        
        -- min12 : 
      in
      {!!}
    (((d1 , c1) , _) ∷ t1 , ∷-Sorted t1 min1 st1) ∨' (((d2 , c2) , _) ∷ t2 , ∷-Sorted t2 min2 st2) | tri≈ _ d1≈d2 _ =
      {!!}
    (((d1 , c1) , _) ∷ t1 , ∷-Sorted t1 min1 st1) ∨' (((d2 , c2) , _) ∷ t2 , ∷-Sorted t2 min2 st2) | tri> _ _ d2<d1 =
      {!!}

    S : BoundedJoinSemilattice l0 l0 l0
    S = record 
      { Carrier = Carrier' 
      ; _≈_ = _≈'_ 
      ; _≤_ = _≤'_
      ; _∨_ = {!!} 
      ; ⊥ = {!!}
      ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
          { isPartialOrder = {!!}
          ; supremum =  {!!}
          }
        ; minimum = {!!} 
        } 
      }
-}
⟦ ProductSemilat isSemilatL isSemilatR ⁂⟧ = record
  { S = S
  ; P = P
  ; i = {!!} , {!!} , {!!}
  ; f = {!!} , {!!} , {!!}
  ; g = {!!} , {!!} , {!!}
  ; inv-S→FP→S = {!!}
  ; inv-FP→S→FP = {!!} 
  }
  where
    open import Data.Product.Relation.Pointwise.NonDependent as PW

    semSemilatL = ⟦ isSemilatL ⁂⟧
    semSemilatR = ⟦ isSemilatR ⁂⟧

    bjsL = SemSemilat.S semSemilatL
    bjsR = SemSemilat.S semSemilatR

    |L| = BoundedJoinSemilattice.Carrier bjsL
    |R| = BoundedJoinSemilattice.Carrier bjsR

    _≈L_ = BoundedJoinSemilattice._≈_ bjsL
    _≈R_ = BoundedJoinSemilattice._≈_ bjsR

    _≤L_ = BoundedJoinSemilattice._≤_ bjsL
    _≤R_ = BoundedJoinSemilattice._≤_ bjsR

    _∨L_ = BoundedJoinSemilattice._∨_ bjsL
    _∨R_ = BoundedJoinSemilattice._∨_ bjsR

    ⊥L = BoundedJoinSemilattice.⊥ bjsL
    ⊥R = BoundedJoinSemilattice.⊥ bjsR

    Carrier' : Set
    Carrier' = |L| × |R| 

    _≈'_ : Rel Carrier' _
    _≈'_ = Pointwise _≈L_ _≈R_

    _≤'_ : Rel Carrier' _
    _≤'_ = Pointwise _≤L_ _≤R_

    _∨'_ : Carrier' → Carrier' → Carrier'
    (aL , aR) ∨' (bL , bR) = (aL ∨L bL) , (aR ∨R bR) 

    ⊥' : Carrier'
    ⊥' = (⊥L , ⊥R)

    minimum' : (z : Carrier') → ⊥' ≤' z
    minimum' (zL , zR) = BoundedJoinSemilattice.minimum bjsL zL , BoundedJoinSemilattice.minimum bjsR zR

    lowerL : (a b : Carrier') → a ≤' (a ∨' b)
    lowerL a@(aL , aR) b@(bL , bR) =
      let
        lowerL-L , _ , _ = BoundedJoinSemilattice.supremum bjsL aL bL 
        lowerL-R , _ , _ = BoundedJoinSemilattice.supremum bjsR aR bR
      in
      lowerL-L , lowerL-R

    lowerR : (a b : Carrier') → b ≤' (a ∨' b)
    lowerR a@(aL , aR) b@(bL , bR) =
      let
        _ , lowerR-L , _ = BoundedJoinSemilattice.supremum bjsL aL bL 
        _ , lowerR-R , _ = BoundedJoinSemilattice.supremum bjsR aR bR
      in
      lowerR-L , lowerR-R

    upper : (a b z : Carrier') → (a ≤' z) → (b ≤' z) → ((a ∨' b) ≤' z)
    upper a@(aL , aR) b@(bL , bR) z@(zL , zR) (aL≤zL ,  aR≤zR) (bL≤zL , bR≤zR) =
      let
        _ , _ , sup-L = BoundedJoinSemilattice.supremum bjsL aL bL 
        _ , _ , sup-R = BoundedJoinSemilattice.supremum bjsR aR bR
      in
      sup-L zL aL≤zL bL≤zL , sup-R zR aR≤zR bR≤zR 

    S : BoundedJoinSemilattice l0 l0 l0
    S = record 
      { Carrier = Carrier' 
      ; _≈_ = _≈'_
      ; _≤_ = _≤'_
      ; _∨_ = _∨'_ 
      ; ⊥ = ⊥'
      ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
          { isPartialOrder = ×-isPartialOrder (BoundedJoinSemilattice.isPartialOrder bjsL)
                                              (BoundedJoinSemilattice.isPartialOrder bjsR)
          ; supremum = λ x → λ y → lowerL x y , lowerR x y , upper x y
          }
        ; minimum = minimum' 
        } 
      }

    
    deltaL = SemSemilat.P semSemilatL
    deltaR = SemSemilat.P semSemilatR

    |L₀| = DeltaPoset.Carrier deltaL
    |R₀| = DeltaPoset.Carrier deltaR
  
    Carrier₀ = |L₀| ⊎ |R₀|
  
    _≈L₀_ = DeltaPoset._≈_ deltaL
    _≈R₀_ = DeltaPoset._≈_ deltaR
    _⊑L₀_ = DeltaPoset._⊑_ deltaL
    _⊑R₀_ = DeltaPoset._⊑_ deltaR
    _∥L₀_ = DeltaPoset._∥_ deltaL
    _∥R₀_ = DeltaPoset._∥_ deltaR
    _∦L₀_ = DeltaPoset._∦_ deltaL
    _∦R₀_ = DeltaPoset._∦_ deltaR
    _<L₀_ = DeltaPoset._<_ deltaL
    _<R₀_ = DeltaPoset._<_ deltaR
    unimL = DeltaPoset.unimodality deltaL
    unimR = DeltaPoset.unimodality deltaR

    P : DeltaPoset {l0} {l0} {l0} {l0}
    P = record
      { Carrier = Carrier₀
      ; _⊑_ = _⊑₀_
      ; _<_ = _<₀_  
      ; _≈_ = SPW.Pointwise _≈L₀_ _≈R₀_
      ; isStrictTotalOrder = ⊎-<-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder deltaL) 
                                                    (DeltaPoset.isStrictTotalOrder deltaR)
      ; isDecPartialOrder = record
        { isPartialOrder = ⊎-isPartialOrder (DeltaPoset.isPartialOrder deltaL) (DeltaPoset.isPartialOrder deltaR)
        ; _≟_ = ⊎-decidable (DeltaPoset._≈?_ deltaL) (DeltaPoset._≈?_ deltaR)
        ; _≤?_ = ⊎-decidable (DeltaPoset._⊑?_ deltaL) (DeltaPoset._⊑?_ deltaR)
        }
      ; unimodality = unimodality
      }
      where
        open import Data.Sum.Relation.Pointwise as SPW
        open import Data.Sum.Relation.LeftOrder

        _⊑₀_ : Carrier₀ → Carrier₀ → Set
        _⊑₀_ = SPW.Pointwise _⊑L₀_ _⊑R₀_ 

        _<₀_ : Carrier₀ → Carrier₀ → Set
        _<₀_ = _<L₀_ ⊎-< _<R₀_

        _∦₀_ : Carrier₀ → Carrier₀ → Set
        a ∦₀ b = a ⊑₀ b ⊎ b ⊑₀ a

        _∥₀_ : Carrier₀ → Carrier₀ → Set
        a ∥₀ b = ¬ (a ∦₀ b)

        unimodality : {a b c : Carrier₀} → a <₀ b → b <₀ c → a ∥₀ b → b ∥₀ c → a ∥₀ c
        unimodality {inj₁ a'} {inj₂ b'} {inj₂ c'} (₁∼₂ tt) (₂∼₂ b'<c') a∥b b∥c (inj₁ (₁∼₂ ())) 
        unimodality {inj₁ a'} {inj₂ b'} {inj₂ c'} (₁∼₂ tt) (₂∼₂ b'<c') a∥b b∥c (inj₂ ())
        unimodality {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c a∦c with a'∥b' | b'∥c' 
          where
            a'∥b' : a' ∥L₀ b'
            a'∥b' (inj₁ a'⊑b') = a∥b $ (inj₁ $ ₁∼₁ a'⊑b')
            a'∥b' (inj₂ b'⊑a') = a∥b $ (inj₂ $ ₁∼₁ b'⊑a')   

            b'∥c' : b' ∥L₀ c'
            b'∥c' (inj₁ b'⊑c') = b∥c $ (inj₁ $ ₁∼₁ b'⊑c')
            b'∥c' (inj₂ c'⊑b') = b∥c $ (inj₂ $ ₁∼₁ c'⊑b')
        unimodality {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c (inj₁ (₁∼₁ a'⊑c')) | a'∥b' | b'∥c' =
          (unimL a'<b' b'<c' a'∥b' b'∥c') (inj₁ a'⊑c')
        unimodality {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c (inj₂ (₁∼₁ c'⊑a')) | a'∥b' | b'∥c' = 
          (unimL a'<b' b'<c' a'∥b' b'∥c') (inj₂ c'⊑a')
        unimodality {inj₁ a'} {inj₁ b'} {inj₂ c'} (₁∼₁ a'<b') (₁∼₂ tt) a∥b b∥c (inj₁ (₁∼₂ ()))
        unimodality {inj₁ a'} {inj₁ b'} {inj₂ c'} (₁∼₁ a'<b') (₁∼₂ tt) a∥b b∥c (inj₂ ())
        unimodality {inj₂ a'} {inj₂ b'} {inj₁ c'} (₂∼₂ a'<b') () a∥b b∥c a∦c
        unimodality {inj₂ a'} {inj₂ b'} {inj₂ c'} (₂∼₂ a'<b') (₂∼₂ b'<c') a∥b b∥c a∦c with a'∥b' | b'∥c'
          where
            a'∥b' : a' ∥R₀ b'
            a'∥b' (inj₁ a'⊑b') = a∥b $ (inj₁ $ ₂∼₂ a'⊑b')
            a'∥b' (inj₂ b'⊑a') = a∥b $ (inj₂ $ ₂∼₂ b'⊑a')   

            b'∥c' : b' ∥R₀ c'
            b'∥c' (inj₁ b'⊑c') = b∥c $ (inj₁ $ ₂∼₂ b'⊑c')
            b'∥c' (inj₂ c'⊑b') = b∥c $ (inj₂ $ ₂∼₂ c'⊑b')
        unimodality {inj₂ a'} {inj₂ b'} {inj₂ c'} (₂∼₂ a'<b') (₂∼₂ b'<c') a∥b b∥c (inj₁ (₂∼₂ a'⊑c')) | a'∥b' | b'∥c' =
          (unimR a'<b' b'<c' a'∥b' b'∥c') (inj₁ a'⊑c')
        unimodality {inj₂ a'} {inj₂ b'} {inj₂ c'} (₂∼₂ a'<b') (₂∼₂ b'<c') a∥b b∥c (inj₂ (₂∼₂ c'⊑a')) | a'∥b' | b'∥c' =
          (unimR a'<b' b'<c' a'∥b' b'∥c') (inj₂ c'⊑a')

⟦ IVarSemilat x ⁂⟧ = {!!}
⟦ PartialSemilat x ⁂⟧ = {!!}
