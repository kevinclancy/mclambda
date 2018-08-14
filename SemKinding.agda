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
⟦ x T⟧ = ?   

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
    _<_ = UnitStrictTotal._lt_

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
  ; unimodality = {!!}
  }
  -- { Carrier =  ×-strictTotalOrder ⟦ isTosetL ⁑⟧ ⟦ isTosetR ⁑⟧
  -- }
  where
    open import Data.Product.Relation.Lex.Strict as LS
    open import Data.Product.Relation.Pointwise.NonDependent as PW
  
    tosetL = ⟦ isTosetL T⟧
    deltaR = ⟦ isDeltaR ⁑⟧
    |L×R| = (StrictTotalOrder.Carrier tosetL) × (DeltaPoset.Carrier deltaR) 
    _L<_ = DeltaPoset._<_  tosetL
    compareL = DeltaPoset.compare tosetL
    _R<_ = DeltaPoset._<_ deltaR
    compareR = DeltaPoset.compare deltaR
    _L⊑_ = DeltaPoset._⊑_  tosetL
    _R⊑_ = DeltaPoset._⊑_ deltaR    
    _L∥_ = DeltaPoset._∥_  tosetL
    _R∥_ = DeltaPoset._∥_ deltaR

    _≈'_ = Pointwise (DeltaPoset._≈_  tosetL) (DeltaPoset._≈_ deltaR)
    _<_ = ×-Lex (DeltaPoset._≈_ tosetL) _L<_ _R<_
    _⊑_ = Pointwise _L⊑_ _R⊑_
    
    _∦_ : Rel |L×R| _
    a ∦ b = a ⊑ b ⊎ b ⊑ a 

    _∥_ : Rel |L×R| _
    a ∥ b = ¬ (a ∦ b)

    ⊑-decPartialOrder : IsPartialOrder _≈'_ _⊑_
    ⊑-decPartialOrder = ×-isPartialOrder (DeltaPoset.isPartialOrder isTosetL) (DeltaPoset.isPartialOrder deltaR)

    ≈'-decidable : Decidable _≈'_
    ≈'-decidable = PW.×-decidable (DeltaPoset._≈?_ deltaL) (DeltaPoset._≈?_ deltaR)

    ⊑-decidable : Decidable _⊑_
    ⊑-decidable = PW.×-decidable (DeltaPoset._⊑?_ deltaL) (DeltaPoset._⊑?_ deltaR)

    <-strict : IsStrictTotalOrder _≈'_ _<_
    <-strict = LS.×-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder deltaL) (DeltaPoset.isStrictTotalOrder deltaR)

    unimodality : {a b c : |L×R|} → a < b → b < c → a ∥ b → b ∥ c → a ∥ c
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₁ aL<bL) (inj₁ bL<cL) a∥b b∥c (inj₁ (aL⊑cL , aR⊑cR)) = 
      {!!}
      where
        unim-L = DeltaPoset.unimodality deltaL

        aL∥bL : aL L∥ bL
        aL∥bL aL∦bL = {!!}

    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₁ aL<bL) (inj₁ bL<cL) a∥b b∥c (inj₂ (cL⊑aL , cR⊑aR)) = {!!}
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₁ aL<bL) (inj₂ (bL≈cL , bR<cR)) a∥b b∥c = {!!}
    unimodality {aL , aR} {bL , bR} {cL , cR} (inj₂ (aL≈bL , aR<bR)) b<c a∥b b∥c = {!!}

⟦ SumToset isTosetL isTosetR ⁑⟧ = {!!}
  where 
    open import Data.Sum.Relation.LeftOrder
    open import Data.Sum.Relation.Pointwise as PW

    deltaL = ⟦ isTosetL ⁑⟧
    deltaR = ⟦ isTosetR ⁑⟧
    CarrierL = DeltaPoset.Carrier deltaL
    CarrierR = DeltaPoset.Carrier deltaR
    _L<_ = DeltaPoset._<_ deltaL
    _R<_ = DeltaPoset._<_ deltaR
    _L⊑_ = DeltaPoset._<_ deltaL
    _R⊑_ = DeltaPoset._<_ deltaR
    _L≈_ =  DeltaPoset._≈_ deltaL
    _R≈_ =  DeltaPoset._≈_ deltaR

    Carrier' = CarrierL ⊎ CarrierR
    _<'_ = _L<_ ⊎-< _R<_
    _⊑'_ = Pointwise _L⊑_ _R⊑_
    _≈'_ = Pointwise _L≈_ _R≈_
 
    tosetLR : IsStrictTotalOrder _≈'_ _<'_ 
    tosetLR = ⊎-<-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder deltaL) (DeltaPoset.isStrictTotalOrder deltaR)
⟦ CapsuleToset isTosetContents ⁑⟧ = {!!}
 
⟦ PartialToset isTosetContents ⁑⟧ = record  
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

    deltaContents = ⟦ isTosetContents ⁑⟧ 
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
    _<ᵀ_ = (_<₀_) ⊎-< (UnitStrictTotal._lt_)

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

⟦_⁂⟧ : ∀ {τ τ₀ : τ} → (isSemilat : IsSemilat τ τ₀) → SemSemilat l0 l0 l0 l0 l0 l0 l0 isSemilat             

⟦_⁂⟧ NatSemilat = record
  { S = S
  ; P = P
  ; i = i
  ; f = |f| , |f|-⊥ , |f|-∨
  ; g = |g| , |g|-⊥ , |g|-∨
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
      ; unimodality = DeltaPoset.unimodality deltaPosetℕ
      }
      where
        deltaPosetℕ = ⟦ NatToset ⁑⟧ 
        
        C = Σ[ n ∈ ℕ ] ¬ (n ≡ 0)
        
        _⊑₀_ : C → C → Set _
        (n1 , p1) ⊑₀ (n2 , p2) = n1 N.≤ n2

        _<₀_ : C → C → Set _
        (n1 , p1) <₀ (n2 , p2) = n1 N.< n2

        _≈₀_ : C → C → Set _
        (n1 , p1) ≈₀ (n2 , p2) = n1 ≡ n2
        
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

    |i| : (DeltaPoset.Carrier P) → (DeltaPoset.Carrier ⟦ NatToset ⁑⟧)
    |i| (n , p) = n

    |i|-monotone : monotone P ⟦ NatToset ⁑⟧ |i|
    |i|-monotone {n , _} {n' , _} n⊑n' = n⊑n'
      
    |i|-monic : monic (DeltaPoset.≈-setoid P) (DeltaPoset.≈-setoid ⟦ NatToset ⁑⟧) |i|
    |i|-monic {a , _} {a' , _} fa≈fa' = fa≈fa' 

    i : P ↣+ ⟦ NatToset ⁑⟧
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

⟦ BoolSemilat ⁂⟧ = {!!}
⟦ DictSemilat x x₁ ⁂⟧ = {!!}
⟦ ProductSemilat x x₁ ⁂⟧ = {!!}
⟦ IVarSemilat x ⁂⟧ = {!!}
⟦ PartialSemilat x ⁂⟧ = {!!}
