module SemKinding where

open import Util

open import Syntax
open import Kinding
open import BoolPoset

open import Level
open import FreeForgetfulAdjunction
open import RelationalStructures

open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Lattice
open import Function.Inverse
open import Data.Product
open import Data.Empty
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Data.Nat as N renaming (_⊔_ to _⊔N_ ; _<_ to _<N_ ; _≤_ to _≤N_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import SemScalars
open import Preorders

⇒-poset : (P : Preorder l0 l0 l0) → (Q : Poset l0 l0 l0) → Poset l0 l0 l0
--[[[
⇒-poset P Q =
  record
  { Carrier = P ⇒ Q'
  ; isPartialOrder = leqPartialOrder
  }
  where
    open import Relation.Binary.OrderMorphism renaming (_⇒-Poset_ to _⇛_)
    |P| : Set
    |P| = Preorder.Carrier P
    _d≈_ : |P| → |P| → Set
    _d≈_ = Preorder._≈_ P
    _d∼_ : |P| → |P| → Set
    _d∼_ = Preorder._∼_ P

    |Q| : Set
    |Q| = Poset.Carrier Q
    Q' = Poset.preorder Q
    _c≈_ : |Q| → |Q| → Set
    _c≈_ = Poset._≈_ Q
    _c≤_ : |Q| → |Q| → Set
    _c≤_ = Poset._≤_ Q
    isPartialOrderCod : IsPartialOrder _c≈_ _c≤_
    isPartialOrderCod = Poset.isPartialOrder Q

    _eq_ : (P ⇒ Q') → (P ⇒ Q') → Set
    f' eq g' = ∀ {v : |P|} → Poset._≈_ Q (f v) (g v)
      where
        f = _⇒_.fun f'
        g = _⇒_.fun g'

    _leq_ : (P ⇒ Q') → (P ⇒ Q') → Set
    f' leq g' = ∀{v : |P|} → (f v) c≤ (g v) 
      where
        f = _⇒_.fun f'
        g = _⇒_.fun g'

    eqRefl : Reflexive _eq_
    eqRefl {f} = Poset.Eq.refl Q

    eqSym : Symmetric _eq_
    eqSym {f} {g} f-eq-g = Poset.Eq.sym Q f-eq-g

    eqTrans : Transitive _eq_
    eqTrans {f} {g} {h} f-eq-g g-eq-h = Poset.Eq.trans Q f-eq-g g-eq-h 

    leqRefl : _eq_ Relation.Binary.⇒ _leq_
    leqRefl {f'} f-eq-f {v} = Poset.reflexive Q f-eq-f 
      where
        f = _⇒_.fun f'

    leqTransitive : Transitive _leq_
    leqTransitive {f'} {g'} {h'} f≤g g≤h {v} = trans≤ fv≤gv gv≤hv 
      where
        f = _⇒_.fun f'
        g = _⇒_.fun g'
        h = _⇒_.fun h'

        fv≤gv : (f v) c≤ (g v)
        fv≤gv = f≤g {v}

        gv≤hv : (g v) c≤ (h v)
        gv≤hv = g≤h {v}

        trans≤ : Transitive _c≤_
        trans≤ = IsPartialOrder.trans isPartialOrderCod

    leqAntisym : Antisymmetric _eq_ _leq_
    leqAntisym {f} {g} f≤g g≤f = Poset.antisym Q f≤g g≤f

    leqPartialOrder : IsPartialOrder _eq_ _leq_
    leqPartialOrder = record
      { isPreorder = record
         { isEquivalence = record
           { refl = λ {x} → eqRefl {x} 
           ; sym = λ {x} {y} → eqSym {x} {y} 
           ; trans = λ {x} {y} {z} → eqTrans {x} {y} {z} 
           }
         ; reflexive = λ {x} {y} → leqRefl {x} {y} 
         ; trans = λ {x} {y} {z} → leqTransitive {x} {y} {z} 
         }
      ;  antisym = λ {x} {y} → leqAntisym {x} {y}
      } 

-- interpretation of poset kinding judgment
⟦_⁎⟧ : ∀ {τ : τ} → IsPoset τ → Poset l0 l0 l0

-- interpret as poset and then upcast to preorder
⟦_⁎⟧' : ∀ {τ : τ} → IsPoset τ → Preorder l0 l0 l0
⟦ wf ⁎⟧' = Poset.preorder ⟦ wf ⁎⟧

record SemStoset {τ : τ} (isStoset : IsStoset τ) : Set l1 where
  field
    T : StrictTotalOrder l0 l0 l0
    eq : StrictTotalOrder.Eq.setoid T ≡ (poset→setoid ⟦ stoset→poset isStoset ⁎⟧)

--SemStoset→sto : {τ : τ} → (isStoset : IsStoset τ) → (semStoset : SemStoset isStoset) → StrictTotalOrder l0 l0 l0
--SemStoset→sto {τ : τ} → 

-- agda-mode: ⁑ is \asterisk, second choice
⟦_⁑⟧ : ∀ {τ : τ} → (p : IsStoset τ) → SemStoset p

⟦_Δ⟧ : ∀ {τ : τ} → IsDeltaPoset τ → DeltaPoset {l0} {l0} {l0} {l0}

-- only that portion of semilattice kinding needed by poset semantics
-- (separating this out allows faster type checking of mutual definitions, which would otherwise take a looong time)
record SemSemilatCore (cₛ ℓₛ₁ ℓₛ₂ cₚ ℓ⊑ₚ ℓ<ₚ ℓ~ₚ : Level) {τ τ₀ : τ} (isSemilat : IsSemilat τ τ₀)
                      : Set (Level.suc $ cₛ ⊔ ℓₛ₁ ⊔ ℓₛ₂ ⊔ cₚ ⊔ ℓ⊑ₚ ⊔ ℓ<ₚ ⊔ ℓ~ₚ) where
  field
    -- direct representation of semilattice
    S : BoundedJoinSemilattice l0 l0 l0
    US : (BoundedJoinSemilattice.poset S) ≡ ⟦ (semilat→poset isSemilat) ⁎⟧
    -- delta poset (freely generates S up-to-isomorphism)
    P : DeltaPoset {cₚ} {ℓ⊑ₚ} {ℓ<ₚ} {ℓ~ₚ}
    -- injection of τ₀ deltaPoset interpretation into P
    i : (DeltaPoset.preorder P) ↣+ ⟦ delta→poset $ semilat→delta isSemilat ⁎⟧' 

-- partial interpretation of semilattice kinding judgment
-- this only includes the portion necessary for mutual recursion with poset kinding interpretation
-- the other portion is implemented in the SemilatKinding directory
⟦_⁂⟧ : ∀ {τ τ₀ : τ} → (isSemilat : IsSemilat τ τ₀) → SemSemilatCore l0 l0 l0 l0 l0 l0 l0 isSemilat   

⟦ FunPoset {q = q} domIsPoset codIsPoset ⁎⟧ = ⇒-poset (⟦ q q⟧ ⟦ domIsPoset ⁎⟧') ⟦ codIsPoset ⁎⟧
⟦ DictPoset domIsToset codIsSemilat ⁎⟧ = 
  ▹-poset (SemStoset.T ⟦ domIsToset ⁑⟧) (SemSemilatCore.S ⟦ codIsSemilat ⁂⟧)
  where
    open import Dictionary
⟦ ProductPoset isPosetL isPosetR ⁎⟧ = ×-poset ⟦ isPosetL ⁎⟧ ⟦ isPosetR ⁎⟧  
  where
    open import Data.Product
    open import Data.Product.Relation.Pointwise.NonDependent
⟦ SumPoset isPosetL isPosetR ⁎⟧ = ⊎-poset {l0} {l0} {l0} {l0} {l0} {l0} ⟦ isPosetL ⁎⟧ ⟦ isPosetR ⁎⟧  
  where
    open import Data.Sum
    open import Data.Sum.Relation.Pointwise
⟦ PartialPoset isPosetContents ⁎⟧ = ⊎-<-poset {l0} {l0} {l0} {l0} {l0} {l0} ⟦ isPosetContents ⁎⟧ unitPoset 
  where
    open import Data.Sum.Relation.LeftOrder
    open import Data.Unit renaming (poset to unitPoset)
⟦ UnitPoset ⁎⟧ = poset
  where
    open import Data.Unit
⟦ BoolPoset ⁎⟧ = B≤-poset
  where
    open import BoolPoset
⟦ NatPoset ⁎⟧ = record 
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _≤_ = _≤_ 
  ; isPartialOrder = ≤-isPartialOrder
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties


⟦ UnitStoset ⁑⟧ = 
  record
  { T = UnitStrictTotal.⊤-strictTotalOrder
  ; eq = PE.refl
  }
⟦ NatStoset ⁑⟧ = 
  record
  { T = <-strictTotalOrder
  ; eq = PE.refl
  }
  where
    open import Data.Nat.Properties
⟦ BoolStoset ⁑⟧ = 
  record
  { T = B<-strictTotalOrder
  ; eq = PE.refl
  }
  where
    open import BoolPoset
⟦ ProductStoset stosetL stosetR ⁑⟧ =
  record
  { T = ×-strictTotalOrder (SemStoset.T ⟦ stosetL ⁑⟧) (SemStoset.T ⟦ stosetR ⁑⟧)
  ; eq = PE.cong₂ ×-setoid (SemStoset.eq ⟦ stosetL ⁑⟧) (SemStoset.eq ⟦ stosetR ⁑⟧)
  }
  where
    open import Data.Product.Relation.Pointwise.NonDependent using (×-setoid)
    open import Data.Product.Relation.Lex.Strict using (×-strictTotalOrder)
⟦ SumStoset stosetL stosetR ⁑⟧ = 
  record
  { T = ⊎-<-strictTotalOrder {l0} {l0} {l0} {l0} {l0} {l0} (SemStoset.T ⟦ stosetL ⁑⟧) (SemStoset.T ⟦ stosetR ⁑⟧)
  ; eq = PE.cong₂ ⊎-setoid (SemStoset.eq ⟦ stosetL ⁑⟧) (SemStoset.eq ⟦ stosetR ⁑⟧)
  }
  where
    open import Data.Sum.Relation.LeftOrder using (⊎-<-strictTotalOrder)
    open import Data.Sum.Relation.Pointwise using (⊎-setoid)
⟦ PartialStoset stosetContents ⁑⟧ =
  record
  { T = ⊎-<-strictTotalOrder {l0} {l0} {l0} {l0} {l0} {l0} (SemStoset.T ⟦ stosetContents ⁑⟧) ⊤-strictTotalOrder  
  ; eq = PE.cong₂ ⊎-setoid (SemStoset.eq ⟦ stosetContents ⁑⟧) PE.refl  
  } 
  where
    open import Data.Sum.Relation.LeftOrder
    open UnitStrictTotal using (⊤-strictTotalOrder)
    open import Data.Sum.Relation.Pointwise using (⊎-setoid)

⟦ UnitDelta Δ⟧ = record
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
⟦ NatDelta Δ⟧ = record
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
    open import Data.Nat.Properties as NP
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
⟦ SumDelta isDeltaL isDeltaR Δ⟧ = sumDeltaPoset
  where 
    open import SumDelta ⟦ isDeltaL Δ⟧ ⟦ isDeltaR Δ⟧

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

------------------------------------------ semilat kinding: comment these out to speed things up

{-
⟦ BoolSemilat ⁂⟧  =
  record
  { S = S
  ; US = PE.refl
  ; P = P
  ; i = |i| , |i|-monotone , |i|-monic
  }
  where
    open import Relation.Binary.Lattice
    open import Relation.Binary.PropositionalEquality as PE using (_≡_)
    open import Relation.Binary.Closure.ReflexiveTransitive
    open import UnitPoset
    open import Data.List
    open import Data.List.Any
    open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
    open import Data.Product
    open import Data.Unit
    open import Data.Empty
    open import Data.Sum
    open import Data.Bool

    open import Relation.Binary
    open import RelationalStructures
    open import Level 
    open import Syntax
    open import Kinding
    open import Util
    open import FreeForgetfulAdjunction
    open import BoolPoset
    open import FinPoset     

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
    P = ⟦ UnitDelta Δ⟧ 

    |i| : (DeltaPoset.Carrier P) → (DeltaPoset.Carrier ⟦ UnitDelta Δ⟧)
    |i| tt = tt

    |i|-monotone : Monotone (DeltaPoset.preorder P) ⟦ delta→poset UnitDelta ⁎⟧' |i|
    |i|-monotone {tt} {tt} tt⊑tt = record {}

    |i|-monic : Injective (DeltaPoset.≈-setoid P) (preorder→setoid ⟦ delta→poset UnitDelta ⁎⟧') |i|
    |i|-monic {tt} {tt} _ = PE.refl 

⟦ NatSemilat ⁂⟧ = 
  record
  { S = S
  ; US = PE.refl
  ; P = P
  ; i = |i| , (λ {p} {p'} z → |i|-monotone {p} {p'} z) , (λ {a} {a'} z → |i|-monic {a} {a'} z)
  }
  where
   open import Data.Nat.Base as NB renaming (_⊔_ to _N⊔_)
   open import Data.Nat.Properties as NP
   open import Data.List.Any
   open import Data.List

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
       open import Relation.Binary renaming (_⇒_ to _⇛_)
       open import Data.List

       deltaPosetℕ = ⟦ NatDelta Δ⟧ 

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
       unimodality = DeltaPoset.unimodality ⟦ NatDelta Δ⟧ 

       <₀-compare : Trichotomous _≈₀_ _<₀_
       <₀-compare (a , _) (b , _) = <-cmp a b

       ⊑₀-reflexive : _≈₀_ ⇛ _⊑₀_
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

   |i| : (DeltaPoset.Carrier P) → (DeltaPoset.Carrier ⟦ NatDelta Δ⟧)
   |i| (n , p) = n

   |i|-monotone : Monotone (DeltaPoset.preorder P) ⟦ delta→poset NatDelta ⁎⟧' |i|
   |i|-monotone {n , _} {n' , _} n⊑n' = n⊑n'

   |i|-monic : Injective (DeltaPoset.≈-setoid P) (preorder→setoid ⟦ delta→poset NatDelta ⁎⟧') |i|
   |i|-monic {a , _} {a' , _} fa≈fa' = fa≈fa' 

   i : (DeltaPoset.preorder P) ↣+ ⟦ delta→poset NatDelta ⁎⟧'
   i = (|i| , (λ {a} → λ {a'} → |i|-monotone {a} {a'}) , (λ {a} → λ {a'} → |i|-monic {a} {a'}))

⟦ ProductSemilat isSemilatL isSemilatR ⁂⟧ =
  record
  { S = S
  ; US = US
  ; P = P
  ; i = |i| , |i|-mono , |i|-injective
  }
  where
    open import Data.List.Relation.Pointwise as LPW hiding (Rel ; Pointwise)
    open import Data.Product.Relation.Pointwise.NonDependent as PW
    open import Data.Sum.Relation.Pointwise hiding (Pointwise)

    semSemilatL = ⟦ isSemilatL ⁂⟧
    semSemilatR = ⟦ isSemilatR ⁂⟧

    bjsL = SemSemilatCore.S semSemilatL
    bjsR = SemSemilatCore.S semSemilatR

    |L| = BoundedJoinSemilattice.Carrier bjsL
    |R| = BoundedJoinSemilattice.Carrier bjsR

    _≈L_ = BoundedJoinSemilattice._≈_ bjsL
    ≈L-refl = BoundedJoinSemilattice.Eq.refl bjsL
    ≈L-reflexive = BoundedJoinSemilattice.Eq.reflexive bjsL
    ≈L-sym = BoundedJoinSemilattice.Eq.sym bjsL
    ≈L-trans = BoundedJoinSemilattice.Eq.trans bjsL
    ≈L-setoid : Setoid _ _
    ≈L-setoid = record
      { Carrier = |L|
      ; isEquivalence = BoundedJoinSemilattice.isEquivalence bjsL
      }
    _≈R_ = BoundedJoinSemilattice._≈_ bjsR
    ≈R-refl = BoundedJoinSemilattice.Eq.refl bjsR
    ≈R-reflexive = BoundedJoinSemilattice.Eq.reflexive bjsR
    ≈R-sym = BoundedJoinSemilattice.Eq.sym bjsR
    ≈R-trans = BoundedJoinSemilattice.Eq.trans bjsR
    ≈R-setoid : Setoid _ _
    ≈R-setoid = record
      { Carrier = |R|
      ; isEquivalence = BoundedJoinSemilattice.isEquivalence bjsR
      }
    _≤L_ = BoundedJoinSemilattice._≤_ bjsL
    _≤R_ = BoundedJoinSemilattice._≤_ bjsR

    _∨L_ = BoundedJoinSemilattice._∨_ bjsL
    _∨R_ = BoundedJoinSemilattice._∨_ bjsR

    ⊥L = BoundedJoinSemilattice.⊥ bjsL
    ⊥R = BoundedJoinSemilattice.⊥ bjsR

    Carrier' : Set
    Carrier' = |L| × |R| 

    infixr 4 _∨'_
    infix 5 _≤'_
    infix 6 _≈'_

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

    US : (BoundedJoinSemilattice.poset S) ≡ ⟦ (ProductPoset (semilat→poset isSemilatL) (semilat→poset isSemilatR)) ⁎⟧
    US = PE.cong₂ (λ x y → ×-poset x y) USL USR
      where
        USL : (BoundedJoinSemilattice.poset bjsL) ≡ ⟦ semilat→poset isSemilatL ⁎⟧
        USL = SemSemilatCore.US semSemilatL

        USR : (BoundedJoinSemilattice.poset bjsR) ≡ ⟦ semilat→poset isSemilatR ⁎⟧
        USR = SemSemilatCore.US semSemilatR

    joinSemilatticeS : JoinSemilattice l0 l0 l0
    joinSemilatticeS = BoundedJoinSemilattice.joinSemiLattice S

    ≈'-refl = BoundedJoinSemilattice.Eq.refl S
    ≈'-reflexive = BoundedJoinSemilattice.Eq.reflexive S
    ≈'-sym = BoundedJoinSemilattice.Eq.sym S

    ≈'-setoid : Setoid _ _
    ≈'-setoid = record
      { Carrier = Carrier'
      ; isEquivalence = ×-isEquivalence (BoundedJoinSemilattice.isEquivalence bjsL) (BoundedJoinSemilattice.isEquivalence bjsR)
      }

    deltaL = SemSemilatCore.P semSemilatL
    deltaR = SemSemilatCore.P semSemilatR

    |L₀| = DeltaPoset.Carrier deltaL
    |R₀| = DeltaPoset.Carrier deltaR

    Carrier₀ = |L₀| ⊎ |R₀|  

    _≈L₀_ : |L₀| → |L₀| → Set  
    _≈L₀_ = DeltaPoset._≈_ deltaL
    ≈L₀-sym = DeltaPoset.sym≈ deltaL
    ≈L₀-refl = DeltaPoset.refl≈ deltaL
    ≈L₀-reflexive = DeltaPoset.reflexive≈ deltaL
    ≈L₀-trans = DeltaPoset.trans≈ deltaL
    ≈L₀-setoid : Setoid _ _
    ≈L₀-setoid = record
      { Carrier = |L₀|
      ; isEquivalence = DeltaPoset.Eq.isEquivalence deltaL
      }
    _≈R₀_ : |R₀| → |R₀| → Set
    _≈R₀_ = DeltaPoset._≈_ deltaR
    unimL = DeltaPoset.unimodality deltaL
    unimR = DeltaPoset.unimodality deltaR

    P : DeltaPoset {l0} {l0} {l0} {l0}
    P = sumDeltaPoset
      where
        open import Data.Sum.Relation.LeftOrder as LO
        open import Data.Sum.Relation.Pointwise as SPW

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

        deltaCarrier = CarrierL ⊎ CarrierR
        _<₀_ = _L<_ ⊎-< _R<_
        _⊑₀_ = SPW.Pointwise _L⊑_ _R⊑_
        _≈₀_ = SPW.Pointwise _L≈_ _R≈_

        _∦₀_ : deltaCarrier → deltaCarrier → Set _
        a ∦₀ b = (a ⊑₀ b) ⊎ (b ⊑₀ a)  

        _∥₀_ : deltaCarrier → deltaCarrier → Set _
        a ∥₀ b = ¬ (a ∦₀ b)

        tosetLR : IsStrictTotalOrder _≈₀_ _<₀_ 
        tosetLR = ⊎-<-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder deltaL) (DeltaPoset.isStrictTotalOrder deltaR)

        partialOrderLR : IsPartialOrder _≈₀_ _⊑₀_
        partialOrderLR = ⊎-isPartialOrder (DeltaPoset.isPartialOrder deltaL) (DeltaPoset.isPartialOrder deltaR)

        ≈₀-equiv : IsEquivalence _≈₀_
        ≈₀-equiv = IsPartialOrder.isEquivalence partialOrderLR

        ≈₀-setoid : Setoid _ _
        ≈₀-setoid = record
          { Carrier = deltaCarrier
          ; isEquivalence = ≈₀-equiv
          }

    
        unimodality : {a b c : deltaCarrier} → a <₀ b → b <₀ c → a ∥₀ b → b ∥₀ c → a ∥₀ c
        unimodality {inj₁ a₀} {inj₂ b₀} {inj₁ c₀} (₁∼₂ .tt) () a∥b b∥c a∦c
        unimodality {inj₁ a₀} {inj₂ b₀} {inj₂ c₀} (₁∼₂ .tt) (₂∼₂ b₀<c₀) a∥b b∥c (inj₁ (₁∼₂ ()))
        unimodality {inj₁ a₀} {inj₂ b₀} {inj₂ c₀} (₁∼₂ .tt) (₂∼₂ b₀<c₀) a∥b b∥c (inj₂ ())
        unimodality {inj₁ a₀} {inj₁ b₀} {inj₂ c₀} (₁∼₁ a₀<b₀) (₁∼₂ .tt) a∥b b∥c (inj₁ (₁∼₂ ()))
        unimodality {inj₁ a₀} {inj₁ b₀} {inj₂ c₀} (₁∼₁ a₀<b₀) (₁∼₂ .tt) a∥b b∥c (inj₂ ())
        unimodality {inj₁ a₀} {inj₁ b₀} {inj₁ c₀} (₁∼₁ a₀<b₀) (₁∼₁ b₀<c₀) a∥b b∥c a∦c with a₀∥b₀ | b₀∥c₀
          where
            a₀∥b₀ : a₀ L∥ b₀
            a₀∥b₀ (inj₁ a₀⊑b₀) = a∥b $ inj₁ (₁∼₁ a₀⊑b₀)
            a₀∥b₀ (inj₂ b₀⊑a₀) = a∥b $ inj₂ (₁∼₁ b₀⊑a₀)

            b₀∥c₀ : b₀ L∥ c₀
            b₀∥c₀ (inj₁ b₀⊑c₀) = b∥c $ inj₁ (₁∼₁ b₀⊑c₀)
            b₀∥c₀ (inj₂ c₀⊑b₀) = b∥c $ inj₂ (₁∼₁ c₀⊑b₀)
        unimodality {inj₁ a₀} {inj₁ b₀} {inj₁ c₀} (₁∼₁ a₀<b₀) (₁∼₁ b₀<c₀) a∥b b∥c (inj₁ (₁∼₁ a₀⊑c₀)) | a₀∥b₀ | b₀∥c₀ =
          (unimL a₀<b₀ b₀<c₀ a₀∥b₀ b₀∥c₀) (inj₁ a₀⊑c₀)
        unimodality {inj₁ a₀} {inj₁ b₀} {inj₁ c₀} (₁∼₁ a₀<b₀) (₁∼₁ b₀<c₀) a∥b b∥c (inj₂ (₁∼₁ c₀⊑a₀)) | a₀∥b₀ | b₀∥c₀ =
          (unimL a₀<b₀ b₀<c₀ a₀∥b₀ b₀∥c₀) (inj₂ c₀⊑a₀)
        unimodality {inj₂ a₀} {inj₂ b₀} {inj₂ c₀} (₂∼₂ a₀<b₀) (₂∼₂ b₀<c₀) a∥b b∥c a∦c with a₀∥b₀ | b₀∥c₀
          where
            a₀∥b₀ : a₀ R∥ b₀
            a₀∥b₀ (inj₁ a₀⊑b₀) = a∥b $ inj₁ (₂∼₂ a₀⊑b₀)
            a₀∥b₀ (inj₂ b₀⊑a₀) = a∥b $ inj₂ (₂∼₂ b₀⊑a₀)

            b₀∥c₀ : b₀ R∥ c₀
            b₀∥c₀ (inj₁ b₀⊑c₀) = b∥c $ inj₁ (₂∼₂ b₀⊑c₀)
            b₀∥c₀ (inj₂ c₀⊑b₀) = b∥c $ inj₂ (₂∼₂ c₀⊑b₀)
        unimodality {inj₂ a₀} {inj₂ b₀} {inj₂ c₀} (₂∼₂ a₀<b₀) (₂∼₂ b₀<c₀) a∥b b∥c (inj₁ (₂∼₂ a₀⊑c₀)) | a₀∥b₀ | b₀∥c₀ =
          (unimR a₀<b₀ b₀<c₀ a₀∥b₀ b₀∥c₀) (inj₁ a₀⊑c₀)
        unimodality {inj₂ a₀} {inj₂ b₀} {inj₂ c₀} (₂∼₂ a₀<b₀) (₂∼₂ b₀<c₀) a∥b b∥c (inj₂ (₂∼₂ c₀⊑a₀)) | a₀∥b₀ | b₀∥c₀ =
          (unimR a₀<b₀ b₀<c₀ a₀∥b₀ b₀∥c₀) (inj₂ c₀⊑a₀)

        sumDeltaPoset : DeltaPoset {_} {_} {_} {_}
        sumDeltaPoset = record  
          { Carrier = deltaCarrier
          ; _⊑_ = _⊑₀_
          ; _<_ = _<₀_
          ; isStrictTotalOrder = tosetLR
          ; isDecPartialOrder = record
            { isPartialOrder = partialOrderLR
            ; _≟_ = SPW.⊎-decidable (DeltaPoset._≈?_ deltaL) (DeltaPoset._≈?_ deltaR) 
            ; _≤?_ = SPW.⊎-decidable (DeltaPoset._⊑?_ deltaL) (DeltaPoset._⊑?_ deltaR) 
            }
          ; unimodality = unimodality
          }

    |P| : Set
    |P| = DeltaPoset.Carrier P

    _≈P_ : |P| → |P| → Set
    _≈P_ = DeltaPoset._≈_ P

    ≈P-setoid : Setoid _ _
    ≈P-setoid = DeltaPoset.≈-setoid P
    ≈P-reflexive = DeltaPoset.Eq.reflexive P
    ≈P-refl = DeltaPoset.Eq.refl P
    ≈P-trans = DeltaPoset.Eq.trans P
    ≈P-sym = DeltaPoset.Eq.sym P

    _<P_ : |P| → |P| → Set
    _<P_ = DeltaPoset._<_ P

    _⊑P_ : |P| → |P| → Set
    _⊑P_ = DeltaPoset._⊑_ P

    _∦P_ : |P| → |P| → Set
    _∦P_ = DeltaPoset._∦_ P

    _∦P?_ = DeltaPoset._∦?_ P
    compareP = DeltaPoset.compare P

    ∦P-sym = DeltaPoset.∦-sym P

    _∥P_ : |P| → |P| → Set
    _∥P_ = DeltaPoset._∥_ P

    iL : (DeltaPoset.preorder $ SemSemilatCore.P semSemilatL) ↣+ ⟦ delta→poset $ semilat→delta isSemilatL ⁎⟧'  
    iL = SemSemilatCore.i semSemilatL

    |iL| : DeltaPoset.Carrier (SemSemilatCore.P semSemilatL) → Preorder.Carrier ⟦ delta→poset $ semilat→delta isSemilatL ⁎⟧'
    |iL| = proj₁ iL

    iL-mono : Monotone (DeltaPoset.preorder $ SemSemilatCore.P semSemilatL) ⟦ delta→poset $ semilat→delta isSemilatL ⁎⟧' |iL|
    iL-mono = proj₁ $ proj₂ iL

    iL-injective : Injective (DeltaPoset.≈-setoid deltaL) (preorder→setoid ⟦ delta→poset $ semilat→delta isSemilatL ⁎⟧') |iL|
    iL-injective = proj₂ $ proj₂ iL

    iR : (DeltaPoset.preorder $ SemSemilatCore.P semSemilatR) ↣+ ⟦ delta→poset $ semilat→delta isSemilatR ⁎⟧' 
    iR = SemSemilatCore.i semSemilatR

    |iR| : DeltaPoset.Carrier (SemSemilatCore.P semSemilatR) → Preorder.Carrier ⟦ delta→poset $ semilat→delta isSemilatR ⁎⟧' 
    |iR| = let |iR| , _ , _ = iR in |iR|

    iR-mono : Monotone (DeltaPoset.preorder $ SemSemilatCore.P semSemilatR) ⟦ delta→poset $ semilat→delta isSemilatR ⁎⟧' |iR|
    iR-mono = let _ , iR-mono , _ = iR in iR-mono

    iR-injective : Injective (DeltaPoset.≈-setoid deltaR) (preorder→setoid ⟦ delta→poset $ semilat→delta isSemilatR ⁎⟧') |iR|
    iR-injective = let _ , _ , iR-injective = iR in iR-injective

    |i| : DeltaPoset.Carrier P → Preorder.Carrier ⟦ delta→poset $ semilat→delta $ ProductSemilat isSemilatL isSemilatR ⁎⟧' 
    |i| (inj₁ x) = inj₁ (|iL| x) 
    |i| (inj₂ x) = inj₂ (|iR| x)

    |i|-mono : Monotone (DeltaPoset.preorder P) ⟦ delta→poset $ semilat→delta $ ProductSemilat isSemilatL isSemilatR ⁎⟧' |i|
    |i|-mono {inj₁ a'} {inj₁ b'} (₁∼₁ a'⊑b') = ₁∼₁ (iL-mono a'⊑b')
    |i|-mono {inj₁ a'} {inj₂ b'} (₁∼₂ ())
    |i|-mono {inj₂ a'} {inj₁ x} ()
    |i|-mono {inj₂ a'} {inj₂ b'} (₂∼₂ a'⊑b') = ₂∼₂ (iR-mono a'⊑b')

    |i|-injective : Injective (DeltaPoset.≈-setoid P) (preorder→setoid ⟦ delta→poset $ semilat→delta $ ProductSemilat isSemilatL isSemilatR ⁎⟧') |i|
    |i|-injective {inj₁ a'} {inj₁ b'} (₁∼₁ ia'≈ib') = ₁∼₁ (iL-injective ia'≈ib')
    |i|-injective {inj₁ a'} {inj₂ b'} (₁∼₂ ())
    |i|-injective {inj₂ a'} {inj₁ b'} ()
    |i|-injective {inj₂ a'} {inj₂ b'} (₂∼₂ ia'≈ib') = ₂∼₂ (iR-injective ia'≈ib')
-}

⟦ PartialSemilat isContentsSemilat ⁂⟧ = 
  record 
  { S = S
  ; US = US
  ; P = P
  ; i = {!!} , {!!} , {!!}
  }
  where
    open import Data.Unit renaming (setoid to unitSetoid ; poset to unitPoset)
    open import Data.Sum.Relation.LeftOrder
    open import Data.Sum

    semContents : SemSemilatCore l0 l0 l0 l0 l0 l0 l0 isContentsSemilat
    semContents = ⟦ isContentsSemilat ⁂⟧ 

    bjsContents : BoundedJoinSemilattice l0 l0 l0
    bjsContents = SemSemilatCore.S semContents

    S : BoundedJoinSemilattice l0 l0 l0
    S = record
      { Carrier = Carrier
      ; _≈_ = SPW.Pointwise (BoundedJoinSemilattice._≈_ bjsContents) _≡_  --(preorder→setoid $ BoundedJoinSemilattice.preorder bjsContents) unitSetoid
      ; _≤_ = _≤ᵀ_
      ; _∨_ = _∨ᵀ_ 
      ; ⊥ = ⊥ᵀ
      ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
          { isPartialOrder = ⊎-<-isPartialOrder (BoundedJoinSemilattice.isPartialOrder bjsContents) 
                                                (Poset.isPartialOrder unitPoset)
          ; supremum = supremum
          }
          ; minimum = minimum
        }
      }
      where
        open UnitStrictTotal using (⊤-strictTotalOrder)
        open import Data.Sum.Relation.Pointwise as SPW using (⊎-setoid)
        Carrier = (BoundedJoinSemilattice.Carrier bjsContents) ⊎ ⊤
        module isBjsContents = IsBoundedJoinSemilattice (BoundedJoinSemilattice.isBoundedJoinSemilattice bjsContents)

        _≤ᵀ_ = (BoundedJoinSemilattice._≤_ bjsContents) ⊎-< (Poset._≤_ unitPoset)
        ⊥ᵀ = inj₁ (BoundedJoinSemilattice.⊥ bjsContents)
        _∨'_ = BoundedJoinSemilattice._∨_ bjsContents

        _∨ᵀ_ : Carrier → Carrier → Carrier 
        inj₁ a ∨ᵀ inj₁ b = inj₁ (a ∨' b)
        inj₁ _ ∨ᵀ inj₂ tt = inj₂ tt
        inj₂ tt ∨ᵀ inj₁ _ = inj₂ tt
        inj₂ tt ∨ᵀ inj₂ tt = inj₂ tt

        upper : (x y : Carrier) → x ≤ᵀ (x ∨ᵀ y) × y ≤ᵀ (x ∨ᵀ y)
        upper (inj₁ x) (inj₁ y) = ₁∼₁ (proj₁ $ isBjsContents.supremum x y) , ₁∼₁ (proj₁ $ proj₂ $ isBjsContents.supremum x y)
        upper (inj₁ x) (inj₂ tt) = ₁∼₂ tt , ₂∼₂ (record {})
        upper (inj₂ tt) (inj₁ x) = ₂∼₂ (record {}) , ₁∼₂ tt
        upper (inj₂ tt) (inj₂ tt) = ₂∼₂ (record {}) , ₂∼₂ (record {})

        least : (x y : Carrier) → (z : Carrier) → (x ≤ᵀ z) → (y ≤ᵀ z) → ((x ∨ᵀ y) ≤ᵀ z)
        least .(inj₁ _) .(inj₁ _) .(inj₂ tt) (₁∼₂ tt) (₁∼₂ tt) = ₁∼₂ tt
        least .(inj₁ _) .(inj₂ _) .(inj₂ _) (₁∼₂ tt) (₂∼₂ (record {})) = ₂∼₂ (record {})
        least (inj₁ x) (inj₁ y) (inj₁ z) (₁∼₁ x≤z) (₁∼₁ y≤z) = ₁∼₁ $ (proj₂ $ proj₂ $ isBjsContents.supremum x y) z x≤z y≤z
        least .(inj₂ _) .(inj₁ _) .(inj₂ _) (₂∼₂ (record {})) (₁∼₂ tt) = ₂∼₂ (record {})
        least .(inj₂ _) .(inj₂ _) .(inj₂ _) (₂∼₂ (record {})) (₂∼₂ (record{})) = ₂∼₂ (record {})

        supremum : Supremum _≤ᵀ_ _∨ᵀ_
        supremum x y = ( (proj₁ $ upper x y) , (proj₂ $ upper x y) , (least x y) )

        minimum : Minimum _≤ᵀ_ ⊥ᵀ 
        minimum (inj₁ x) = ₁∼₁ (isBjsContents.minimum x)
        minimum (inj₂ tt) = ₁∼₂ tt

    US : (BoundedJoinSemilattice.poset S) ≡ ⟦ semilat→poset (PartialSemilat isContentsSemilat) ⁎⟧ 
    US = PE.cong₂ (⊎-<-poset {l0} {l0} {l0} {l0} {l0} {l0}) (SemSemilatCore.US semContents) PE.refl

    P : DeltaPoset {l0} {l0} {l0} {l0}
    P = record
      { Carrier = Carrier₀
      ; _⊑_ = _≤₀_
      ; _<_ = _<₀_
      ; _≈_ = _≈₀_
      ; isStrictTotalOrder = ⊎-<-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder P') (UnitStrictTotal.⊤-IsStrictTotalOrder)
      ; isDecPartialOrder = record
        { isPartialOrder = ⊎-<-isPartialOrder (IsDecPartialOrder.isPartialOrder isDecPartialOrder₀) 
                                               (Poset.isPartialOrder unitPoset)
        ; _≟_ = _≟₀_
        ; _≤?_ = _≤₀?_
        } 
      ; unimodality = unimodality
      } 
      where
        open import Data.Sum.Relation.Pointwise as SPW using (⊎-setoid)

        P' : DeltaPoset {l0} {l0} {l0} {l0}
        P' = SemSemilatCore.P semContents

        isDecPartialOrder₀ : IsDecPartialOrder (DeltaPoset._≈_ P') (DeltaPoset._⊑_ P')
        isDecPartialOrder₀ = DeltaPoset.isDecPartialOrder P'

        Carrier₀ : Set
        Carrier₀ = (DeltaPoset.Carrier P') ⊎ ⊤

        _≈₀_ : Carrier₀ → Carrier₀ → Set
        _≈₀_ = SPW.Pointwise (DeltaPoset._≈_ P') _≡_

        _≟₀_ : Decidable _≈₀_
        inj₁ a ≟₀ inj₁ b with IsDecPartialOrder._≟_ isDecPartialOrder₀ a b 
        inj₁ a ≟₀ inj₁ b | yes a≈b = yes $ ₁∼₁ a≈b 
        inj₁ a ≟₀ inj₁ b | no ¬a≈b = no ¬inj₁a≈₀inj₁b
          where
            ¬inj₁a≈₀inj₁b : ¬ (inj₁ a ≈₀ inj₁ b)
            ¬inj₁a≈₀inj₁b (₁∼₁ a≈b) = ¬a≈b a≈b
        inj₁ a ≟₀ inj₂ tt = no ¬inj₁a≈₀inj₂tt
          where
            ¬inj₁a≈₀inj₂tt : ¬ (inj₁ a ≈₀ inj₂ tt)
            ¬inj₁a≈₀inj₂tt (₁∼₂ ())
        inj₂ tt ≟₀ inj₁ b = no (λ ())
        inj₂ tt ≟₀ inj₂ tt = yes (₂∼₂ PE.refl)

        _≤₀_ : Carrier₀ → Carrier₀ → Set
        _≤₀_ = (DeltaPoset._⊑_ P') ⊎-< (Poset._≤_ unitPoset)

        _≤₀?_ : Decidable _≤₀_
        inj₁ a ≤₀? inj₁ b with IsDecPartialOrder._≤?_ isDecPartialOrder₀ a b
        inj₁ a ≤₀? inj₁ b | yes a≤b = yes $ ₁∼₁ a≤b
        inj₁ a ≤₀? inj₁ b | no ¬a≤b = no $ ¬inj₁a≤₀inj₁b
          where
            ¬inj₁a≤₀inj₁b : ¬ (inj₁ a ≤₀ inj₁ b)
            ¬inj₁a≤₀inj₁b (₁∼₁ a≤b) = ¬a≤b a≤b
        inj₁ a ≤₀? inj₂ tt = yes (₁∼₂ tt)
        inj₂ tt ≤₀? inj₁ b = no (λ ())
        inj₂ tt ≤₀? inj₂ tt = yes (₂∼₂ (record {}))

        _<₀_ : Carrier₀ → Carrier₀ → Set
        _<₀_ = (DeltaPoset._<_ P') ⊎-< (UnitStrictTotal._⊤<_)

        _∦₀_ : Carrier₀ → Carrier₀ → Set
        a ∦₀ b = (a ≤₀ b) ⊎ (b ≤₀ a) 
      
        _∥₀_ : Carrier₀ → Carrier₀ → Set
        a ∥₀ b = ¬ (a ∦₀ b)

        _∥_ = DeltaPoset._∥_ P'
        _∦_ = DeltaPoset._∦_ P'
        _⊑_ = DeltaPoset._⊑_ P'

        unimodality : {a b c : Carrier₀} → (a <₀ b) → (b <₀ c) → (a ∥₀ b) → (b ∥₀ c) → (a ∥₀ c)
        unimodality {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c = a∥c
          where
            a'∥b' : a' ∥ b'
            a'∥b' (inj₁ a'⊑b') = a∥b (inj₁ $ ₁∼₁ a'⊑b')
            a'∥b' (inj₂ b'⊑a') = a∥b (inj₂ $ ₁∼₁ b'⊑a')

            b'∥c' : b' ∥ c'
            b'∥c' (inj₁ b'⊑c') = b∥c (inj₁ $ ₁∼₁ b'⊑c')
            b'∥c' (inj₂ c'⊑b') = b∥c (inj₂ $ ₁∼₁ c'⊑b')

            a'∥c' : a' ∥ c'
            a'∥c' = (DeltaPoset.unimodality P') a'<b' b'<c' a'∥b' b'∥c' 

            a∥c : (inj₁ a') ∥₀ (inj₁ c')
            a∥c (inj₁ (₁∼₁ a'⊑c')) = a'∥c' (inj₁ a'⊑c')
            a∥c (inj₂ (₁∼₁ c'⊑a')) = a'∥c' (inj₂ c'⊑a')
        unimodality {inj₁ a'} {inj₁ b'} {inj₂ tt} (₁∼₁ a'⊑b') (₁∼₂ tt) a∥b b∥c = ⊥-elim $ b∥c (inj₁ (₁∼₂ tt))
        unimodality {inj₁ x} {inj₂ y} {c} a<b b<c a∥b b∥c = ⊥-elim $ a∥b (inj₁ (₁∼₂ tt))
        unimodality {inj₂ y} {inj₁ x} {c} () b<c a∥b b∥c
        unimodality {inj₂ y} {inj₂ y₁} {c} (₂∼₂ ()) b<c a∥b b∥c
