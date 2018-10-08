
module SemPoset where


open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Data.Sum
open import Data.Product

open import Syntax
open import Kinding
open import Util
open import SemScalars
open import Preorders
--open import SemSemilatKinding

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

mutual
  ⟦_⁎⟧ : ∀ {τ : τ} → IsPoset τ → Poset l0 l0 l0
  ⟦ FunPoset {q = q} domIsPoset codIsPoset ⁎⟧ = ⇒-poset (⟦ q q⟧ ⟦ domIsPoset ⁎⟧') ⟦ codIsPoset ⁎⟧
  ⟦ DictPoset domIsToset codIsSemilat ⁎⟧ = 
    ▹-poset {!!} {!⟦ codIsSemilat ⁂⟧!} -- ⟦ domIsToset ⁑⟧ ⟦ codIsSemilat ⁂⟧   
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

  ⟦_⁎⟧' : ∀ {τ : τ} → IsPoset τ → Preorder l0 l0 l0
  ⟦ wf ⁎⟧' = Poset.preorder ⟦ wf ⁎⟧
