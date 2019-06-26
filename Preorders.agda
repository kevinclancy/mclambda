module Preorders where

open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum
open import Data.Sum.Relation.Pointwise
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.Lattice
open import Function as F using (_$_)
open import Level

open import Util
open Preorder

record _⇒_ {p₁ p₂ p₃ p₄ p₅ p₆}
                     (P₁ : Preorder p₁ p₂ p₃)
                     (P₂ : Preorder p₄ p₅ p₆) : Set (p₁ ⊔ p₃ ⊔ p₄ ⊔ p₆) where
  field
    fun : Carrier P₁ → Carrier P₂
    monotone : Preorder._∼_ P₁ =[ fun ]⇒ Preorder._∼_ P₂

id : ∀ {p₁ p₂ p₃} {P : Preorder p₁ p₂ p₃} → P ⇒ P
id = record
  { fun      = F.id
  ; monotone = F.id
  }

_∘_ : ∀ {p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉}
        {P₁ : Preorder p₁ p₂ p₃}
        {P₂ : Preorder p₄ p₅ p₆}
        {P₃ : Preorder p₇ p₈ p₉} →
      P₂ ⇒ P₃ → P₁ ⇒ P₂ → P₁ ⇒ P₃
f ∘ g = record
  { fun      = F._∘_ (_⇒_.fun f)      (_⇒_.fun g)
  ; monotone = F._∘_ (_⇒_.monotone f) (_⇒_.monotone g)
  }

infixl 0 _>>_
_>>_ : {P Q R : Preorder l0 l0 l0} → P ⇒ Q → Q ⇒ R → P ⇒ R
_>>_ {P} {Q} {R} f g = g ∘ f

⊎-preorder0 : Preorder l0 l0 l0 → Preorder l0 l0 l0 → Preorder l0 l0 l0
⊎-preorder0 = ⊎-preorder {l0} {l0} {l0} {l0} {l0} {l0}

⇒-preorder : (P Q : Preorder l0 l0 l0) → Preorder l0 l0 l0
--[[[
⇒-preorder P Q =
  record
  { Carrier = P ⇒ Q
  ; isPreorder = leqPreorder
  }
  where
    |P| : Set
    |P| = Preorder.Carrier P
    _d≈_ : |P| → |P| → Set
    _d≈_ = Preorder._≈_ P
    _d∼_ : |P| → |P| → Set
    _d∼_ = Preorder._∼_ P
    
    |Q| : Set
    |Q| = Preorder.Carrier Q
    _c≈_ : |Q| → |Q| → Set
    _c≈_ = Preorder._≈_ Q
    _c∼_ : |Q| → |Q| → Set
    _c∼_ = Preorder._∼_ Q
    isPreorderCod : IsPreorder _c≈_ _c∼_
    isPreorderCod = Preorder.isPreorder Q

    _eq_ : (P ⇒ Q) → (P ⇒ Q) → Set
    f' eq g' = ∀ {v : |P|} → Preorder._≈_ Q (f v) (g v)
      where
        f = _⇒_.fun f'
        g = _⇒_.fun g'

    _leq_ : (P ⇒ Q) → (P ⇒ Q) → Set
    f' leq g' = ∀{v : |P|} → (f v) c∼ (g v) 
      where
        f = _⇒_.fun f'
        g = _⇒_.fun g'
        
    eqRefl : Reflexive _eq_
    eqRefl {f} = Preorder.Eq.refl Q

    eqSym : Symmetric _eq_
    eqSym {f} {g} f-eq-g = Preorder.Eq.sym Q f-eq-g

    eqTrans : Transitive _eq_
    eqTrans {f} {g} {h} f-eq-g g-eq-h = Preorder.Eq.trans Q f-eq-g g-eq-h 

    leqRefl : _eq_ Relation.Binary.⇒ _leq_
    leqRefl {f'} f-eq-f {v} = Preorder.reflexive Q f-eq-f 
      where
        f = _⇒_.fun f'

    leqTransitive : Transitive _leq_
    leqTransitive {f'} {g'} {h'} f≤g g≤h {v} = trans≤ fv≤gv gv≤hv 
      where
        f = _⇒_.fun f'
        g = _⇒_.fun g'
        h = _⇒_.fun h'

        fv≤gv : (f v) c∼ (g v)
        fv≤gv = f≤g {v}

        gv≤hv : (g v) c∼ (h v)
        gv≤hv = g≤h {v}

        trans≤ : Transitive _c∼_
        trans≤ = IsPreorder.trans isPreorderCod

    leqPreorder : IsPreorder _eq_ _leq_
    leqPreorder = record
      { isEquivalence = record
        { refl = λ {x} → eqRefl {x} 
        ; sym = λ {x} {y} → eqSym {x} {y} 
        ; trans = λ {x} {y} {z} → eqTrans {x} {y} {z} 
        }
      ; reflexive = λ {x} {y} → leqRefl {x} {y} 
      ; trans = λ {x} {y} {z} → leqTransitive {x} {y} {z} 
      }
--]]]

▹-preorder : (T₀ : StrictTotalOrder l0 l0 l0) → (V : BoundedJoinSemilattice l0 l0 l0) → Preorder l0 l0 l0
▹-preorder T₀ V = Poset.preorder (▹-poset T₀ V)
  where
    open import Dictionary

⌈⌉-preorder : (T₀ : StrictTotalOrder l0 l0 l0) → Preorder l0 l0 l0
⌈⌉-preorder T₀ = Poset.preorder (⌈⌉-poset T₀)
  where
    open import IVar

partial-preorder : (P : Preorder l0 l0 l0) → Preorder l0 l0 l0
partial-preorder P = ⊎-<-preorder P (Poset.preorder unitPoset)
  where
    open import Data.Sum.Relation.LeftOrder
    open import Data.Unit.Properties renaming (≤-poset to unitPoset)
