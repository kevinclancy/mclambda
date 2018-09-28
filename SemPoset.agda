
module SemPoset where

open import Syntax
open import Kinding
open import Util

open import Relation.Binary
open import Data.Sum
open import Data.Product

open import Relation.Binary.PropositionalEquality as PE using (_≡_)

⟦_⁎⟧ : ∀ {τ : τ} → IsPoset τ → Poset l0 l0 l0
⟦ FunPoset {q = q} domIsPoset codIsPoset ⁎⟧ = 
  record{ 
    Carrier = D⇒C ;
    _≈_ = _eq_ ;
    _≤_ = _leq_ ;
    isPartialOrder = leqPartialOrder -- leqPartialOrder 
   }  
  where
    domPoset : Poset l0 l0 l0
    domPoset = ⟦ domIsPoset ⁎⟧ 
    
    codPoset : Poset l0 l0 l0
    codPoset = ⟦ codIsPoset ⁎⟧

    D : Set
    D = Poset.Carrier domPoset
    _d≈_ : D → D → Set
    _d≈_ = Poset._≈_ domPoset
    _d≤_ : D → D → Set
    _d≤_ = Poset._≤_ domPoset
    
    C : Set
    C = Poset.Carrier codPoset
    _c≈_ : C → C → Set
    _c≈_ = Poset._≈_ codPoset
    _c≤_ : C → C → Set
    _c≤_ = Poset._≤_ codPoset
    isPartialOrderCod : IsPartialOrder _c≈_ _c≤_
    isPartialOrderCod = Poset.isPartialOrder codPoset
    
    D⇒C : Set
    D⇒C = Σ[ f ∈ (D → C) ] (∀{v₁ v₂ : D} → v₁ d≤ v₂ → (f v₁) c≤ (f v₂))

    _eq_ : D⇒C → D⇒C → Set
    (f , _) eq (g , _) = ∀ {v : D} → Poset._≈_ codPoset (f v) (g v)

    _leq_ : D⇒C → D⇒C → Set
    (f , _) leq (g , _) = ∀{v : D} → (f v) c≤ (g v) 

    eqRefl : Reflexive _eq_
    eqRefl {f} = Poset.Eq.refl codPoset

    eqSym : Symmetric _eq_
    eqSym {f} {g} f-eq-g = Poset.Eq.sym codPoset f-eq-g

    eqTrans : Transitive _eq_
    eqTrans {f} {g} {h} f-eq-g g-eq-h = Poset.Eq.trans codPoset f-eq-g g-eq-h 

    leqRefl : _eq_ ⇒ _leq_
    leqRefl {(f , _)} f-eq-f {v} = Poset.reflexive codPoset f-eq-f 

    leqTransitive : Transitive _leq_
    leqTransitive {(f , _)} {(g , _)} {(h , _)} f≤g g≤h {v} = trans≤ fv≤gv gv≤hv 
      where
        fv≤gv : (f v) c≤ (g v)
        fv≤gv = f≤g {v}

        gv≤hv : (g v) c≤ (h v)
        gv≤hv = g≤h {v}

        trans≤ : Transitive _c≤_
        trans≤ = IsPartialOrder.trans isPartialOrderCod

    leqAntisym : Antisymmetric _eq_ _leq_
    leqAntisym {f} {g} f≤g g≤f = Poset.antisym codPoset f≤g g≤f
        
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
