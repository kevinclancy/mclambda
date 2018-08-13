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

-- agda-mode: ⁑ is \asterisk, second choice
⟦_⁑⟧ : ∀ {τ : τ} → IsToset τ → DeltaPoset {l0} {l0} {l0} {l0}
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

    unimodality : {a b c : ⊤} → a < b → b < c → a ∥ b → b ∥ c → a ∥ c
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
      
⟦ BoolToset ⁑⟧ = {!!}
⟦ ProductToset isTosetL isTosetR ⁑⟧ = record
  { Carrier = (DeltaPoset.Carrier deltaL) × (DeltaPoset.Carrier deltaR) 
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

    deltaL = ⟦ isTosetL ⁑⟧
    deltaR = ⟦ isTosetR ⁑⟧
    _L<_ = DeltaPoset._<_ deltaL
    compareL = DeltaPoset.compare deltaL
    _R<_ = DeltaPoset._<_ deltaR
    compareR = DeltaPoset.compare deltaR
    _L⊑_ = DeltaPoset._⊑_ deltaL
    _R⊑_ = DeltaPoset._⊑_ deltaR    
    _≈'_ = Pointwise (DeltaPoset._≈_ deltaL) (DeltaPoset._≈_ deltaR)

    _<_ = ×-Lex (DeltaPoset._≈_ deltaL) _L<_ _R<_
    _⊑_ = Pointwise _L⊑_ _R⊑_

    ⊑-decPartialOrder : IsPartialOrder _≈'_ _⊑_
    ⊑-decPartialOrder = ×-isPartialOrder (DeltaPoset.isPartialOrder deltaL) (DeltaPoset.isPartialOrder deltaR)

    ≈'-decidable : Decidable _≈'_
    ≈'-decidable = PW.×-decidable (DeltaPoset._≈?_ deltaL) (DeltaPoset._≈?_ deltaR)

    ⊑-decidable : Decidable _⊑_
    ⊑-decidable = PW.×-decidable (DeltaPoset._⊑?_ deltaL) (DeltaPoset._⊑?_ deltaR)

    <-strict : IsStrictTotalOrder _≈'_ _<_
    <-strict = LS.×-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder deltaL) (DeltaPoset.isStrictTotalOrder deltaR)

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
  ; f = {!!}
  ; g = {!!}
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
 
⟦ BoolSemilat ⁂⟧ = {!!}
⟦ DictSemilat x x₁ ⁂⟧ = {!!}
⟦ ProductSemilat x x₁ ⁂⟧ = {!!}
⟦ IVarSemilat x ⁂⟧ = {!!}
⟦ PartialSemilat x ⁂⟧ = {!!}
