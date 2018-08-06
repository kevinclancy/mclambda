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
open import Level
open import Util using (l0;l1;l2)
open import Data.Unit renaming (preorder to unitPreorder ; decTotalOrder to unitToset )
open import Data.Nat as N hiding (_<_)
open import Data.Nat.Properties as NP
open import Data.Bool
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import FreeForgetfulAdjunction
open import RelationalStructures
open Util

-- record SemPoset {ℓ₁} : Set (suc ℓ₁) where
--   field
--     -- An agda type which serves represents a λMC type 
--     A : Set 
--     -- A partial order on A
--     _⊑_ : Rel A ℓ₁    
--     -- Proof that it's actually a partial order
--     isPartialOrder : IsPartialOrder _⊑_ 


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

-- agda-mode: ⁑ is \asterisk, second choice
⟦_⁑⟧ : ∀ {τ : τ} → IsToset τ → DeltaPoset0
⟦ UnitToset ⁑⟧ = record
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
    _<_ = UnitStrictTotal._lt_

    _∦_ : ⊤ → ⊤ → Set
    x ∦ y = x ⊤≤ y ⊎ y ⊤≤ x
    
    _∥_ : ⊤ → ⊤ → Set
    _∥_ x y = ¬ (x ∦ y)

    unimodality : {a b c d : ⊤} → a < b → b < c → d ∦ a → d ∥ b → d ∥ c
    unimodality () () _ _

⟦ NatToset ⁑⟧ = record
  { Carrier = ℕ 
  ; _⊑_ = _⊑_
  ; _<_ = _<_
  ; isStrictTotalOrder = NP.<-isStrictTotalOrder
  ; isDecPartialOrder = record
    { isPartialOrder = natPartialOrder
    ; _≟_ = IsDecEquivalence._≟_ ≡-isDecEquivalence
    ; _≤?_ = N._≤?_
    }
  ; unimodality = {!unimodality!}
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

    unimodality : {a b c d : ℕ} → a < b → b < c → d ∦ a → d ∥ b → d ∥ c
    unimodality {a} {b} {c} {d} _ _ _ d∥b = ⊥-elim $ d∥b (≤-total d b)
      
⟦ BoolToset ⁑⟧ = {!!}
⟦ ProductToset isTosetL isTosetR ⁑⟧ =
  {!!}
  -- { Carrier =  ×-strictTotalOrder ⟦ isTosetL ⁑⟧ ⟦ isTosetR ⁑⟧
  -- }
  where
    open import Data.Product.Relation.Lex.Strict as LS
    open import Data.Product.Relation.Pointwise.NonDependent as PW

    deltaL = ⟦ isTosetL ⁑⟧
    deltaR = ⟦ isTosetR ⁑⟧
    _L<_ = DeltaPoset0._<_ deltaL
    compareL = DeltaPoset0.compare deltaL
    _R<_ = DeltaPoset0._<_ deltaR
    compareR = DeltaPoset0.compare deltaR
    _L⊑_ = DeltaPoset0._⊑_ deltaL
    _R⊑_ = DeltaPoset0._⊑_ deltaR    
    
    _<_ = ×-Lex _≡_ _L<_ _R<_
    _⊑_ = Pointwise _L⊑_ _R⊑_

    ⊑-decPartialOrder : IsDecPartialOrder _≡_ _⊑_
    ⊑-decPartialOrder = {!!}

    <-strict : IsStrictTotalOrder _≡_ _<_
    <-strict = record
      { isEquivalence = PE.isEquivalence
      ; trans = IsStrictTotalOrder.trans p
      ; compare = comp
      }
      where
        p : IsStrictTotalOrder (Pointwise _≡_ _≡_) _<_
        p = LS.×-isStrictTotalOrder (DeltaPoset0.isStrictTotalOrder deltaL) (DeltaPoset0.isStrictTotalOrder deltaR)

        comp : Trichotomous _≡_ _<_
        comp x@(xL , xR) y@(yL , yR) with compareL xL yL 
        comp x@(xL , xR) y@(yL , yR) | tri< xL<yL ¬xL≡yL ¬yL<xL = 
          tri< x<y ¬x≡y ¬y<x
          where
            x<y : x < y
            x<y = inj₁ xL<yL

            ¬x≡y : ¬ x ≡ y
            ¬x≡y x≡y = ¬xL≡yL $ proj₁ (≡⇒≡×≡ x≡y) 

            ¬y<x : ¬ y < x
            ¬y<x (inj₁ yL<xL) = ¬yL<xL yL<xL
            ¬y<x (inj₂ (yL≡xL , yR⊑xR)) = ¬xL≡yL (PE.sym yL≡xL) 
        
        comp x@(xL , xR) y@(yL , yR) | tri≈ ¬xL<yL xL≡yL ¬yL<xL with compareR xR yR
        comp x@(xL , xR) y@(yL , yR) | tri≈ ¬xL<yL xL≡yL ¬yL<xL | tri< xR<yR ¬xR≡yR ¬yR<xR =
          tri< (inj₂ $ xL≡yL , xR<yR) ¬x≡y ¬y<x
          where
            ¬x≡y : ¬ x ≡ y
            ¬x≡y x≡y = ¬xR≡yR $ proj₂ (≡⇒≡×≡ x≡y) 

            ¬y<x : ¬ y < x
            ¬y<x (inj₁ yL<xL) = ¬yL<xL yL<xL
            ¬y<x (inj₂ (yL≡xL , yR<xR)) = ¬yR<xR yR<xR 
        comp x@(xL , xR) y@(yL , yR) | tri≈ ¬xL<yL xL≡yL ¬yL<xL | tri≈ ¬xR<yR xR≡yR ¬yR<xR =
          tri≈ ¬x<y (≡×≡⇒≡ $ xL≡yL , xR≡yR) ¬y<x 
          where
            ¬x<y : ¬ x < y
            ¬x<y (inj₁ xL<yL) = ¬xL<yL xL<yL
            ¬x<y (inj₂ (xL≡yL , xR<yR)) = ¬xR<yR xR<yR

            ¬y<x : ¬ y < x
            ¬y<x (inj₁ yL<xL) = ¬yL<xL yL<xL
            ¬y<x (inj₂ (yL≡xL , yR<xR)) = ¬yR<xR yR<xR

        comp x@(xL , xR) y@(yL , yR) | tri≈ ¬xL<yL xL≡yL ¬yL<xL | tri> ¬xR<yR ¬xR≡yR yR<xR =
          tri> ¬x<y ¬x≡y (inj₂ $ (PE.sym xL≡yL) , yR<xR)
          where
            ¬x<y : ¬ x < y
            ¬x<y (inj₁ xL<yL) = ¬xL<yL xL<yL
            ¬x<y (inj₂ (xL≡yL , xR<yR)) = ¬xR<yR xR<yR

            ¬x≡y : ¬ x ≡ y
            ¬x≡y x≡y = ¬xR≡yR (proj₂ $ ≡⇒≡×≡ x≡y)

        comp x@(xL , xR) y@(yL , yR) | tri> ¬xL<yL ¬xL≡yL yL<xL =
          tri> ¬x<y ¬x≡y (inj₁ yL<xL)
          where
            ¬x<y : ¬ x < y
            ¬x<y (inj₁ xL<yL) = ¬xL<yL xL<yL
            ¬x<y (inj₂ (xL≡yL , xR<yR)) = ¬xL≡yL xL≡yL
          
            ¬x≡y : ¬ x ≡ y
            ¬x≡y x≡y = ¬xL≡yL (proj₁ $ ≡⇒≡×≡ x≡y)

⟦ SumToset isTosetL isTosetR ⁑⟧ = {!!}
  where 
    open import Data.Sum.Relation.LeftOrder
    --tosetLR : StrictTotalOrder0
    --tosetLR = ⊎-<-strictTotalOrder {l0} {l0} {l0} {l0} {l0} {l0} ⟦ isTosetL ⁑⟧ ⟦ isTosetR ⁑⟧
⟦ CapsuleToset isTosetContents ⁑⟧ = {!!}
 
⟦ PartialToset isTosetContents ⁑⟧ = record  
  { Carrier = |Cᵀ|
  ; _⊑_ = _⊑ᵀ_
  ; _<_ = _<ᵀ_
  ; isStrictTotalOrder = <ᵀ-strict
  ; isDecPartialOrder = record
    { isPartialOrder = ⊑ᵀ-partial
    ; _≟_ = IsDecEquivalence._≟_ ≡-isDecEquivalence
    ; _≤?_ = N._≤?_
    }
  ; unimodality = {!unimodality!}
  }
  where
    open import UnitPoset
    open UnitStrictTotal
    open import Data.Sum.Relation.LeftOrder

    deltaContents = ⟦ isTosetContents ⁑⟧ 
    |C| = DeltaPoset0.Carrier deltaContents
    _<'_ = DeltaPoset0._<_ deltaContents
    _⊑'_ = DeltaPoset0._⊑_ deltaContents
    
    -- -ᵀ Carrier
    |Cᵀ| : Set
    |Cᵀ| = |C| ⊎ ⊤

    _<ᵀ_ : |Cᵀ| → |Cᵀ| → Set
    _<ᵀ_ = (_<'_) ⊎-< (UnitStrictTotal._lt_)

    <ᵀ-strict = ⊎-<-isStrictTotalOrder (DeltaPoset0.isStrictTotalOrder deltaContents) ⊤-IsStrictTotalOrder


    _⊑ᵀ_ : |Cᵀ| → |Cᵀ| → Set
    _⊑ᵀ_ = (_⊑'_) ⊎-< (_⊤≤_)  

    ⊑ᵀ-partial = 
      ⊎-<-isPartialOrder
        (DeltaPoset0.isPartialOrder deltaContents) 
        (IsDecPartialOrder.isPartialOrder ⊤≤-isDecPartialOrder)

    ⊑ᵀ-decidable =
      ⊎-<-decidable
        (DeltaPoset0._⊑?_ deltaContents)
        _⊤≤?_
open import Relation.Binary.Lattice


⟦_⁂⟧ : ∀ {τ τ₀ : τ} → IsSemilat τ τ₀ → BoundedJoinSemilattice0 × DeltaPoset0
⟦ NatSemilat ⁂⟧ = {!!}
⟦ BoolSemilat ⁂⟧ = {!!}
⟦ DictSemilat x x₁ ⁂⟧ = {!!}
⟦ ProductSemilat x x₁ ⁂⟧ = {!!}
⟦ IVarSemilat x ⁂⟧ = {!!}
⟦ PartialSemilat x ⁂⟧ = {!!}
