module Preorders where

open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum
open import Data.Sum.Relation.Pointwise
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.OrderMorphism renaming (_⇒-Preorder_ to _⇒_)
open import Function using (_$_)

open import Util

⊎-preorder0 : Preorder l0 l0 l0 → Preorder l0 l0 l0 → Preorder l0 l0 l0
⊎-preorder0 = ⊎-poset {l0} {l0} {l0} {l0} {l0} {l0}

_⟨×⟩_ : {P Q R S : Preorder l0 l0 l0} → P ⇒ Q → R ⇒ S → (×-poset P R) ⇒ (×-poset Q S)
--[[[
_⟨×⟩_ {P} {Q} {R} {S} f g = record 
  { fun = fun
  ; monotone = monotone
  }  
  where
    open Preorder

    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q
    |R| = Preorder.Carrier R
    |S| = Preorder.Carrier S

    |f| : |P| → |Q|
    |f| = _⇒_.fun f

    |g| : |R| → |S|
    |g| = _⇒_.fun g

    fun : |P| × |R| → |Q| × |S|
    fun (p , r) = |f| p , |g| r

    monotone : _≤_ (×-poset P R) =[ fun ]⇒ _≤_ (×-poset Q S)
    monotone {p₁ , r₁} {p₂ , r₂} (p₁≤p₂ , r₁≤r₂) = (_⇒_.monotone f p₁≤p₂ , _⇒_.monotone g r₁≤r₂)
--]]]

⟨_,_⟩ : {P Q R : Preorder l0 l0 l0} → P ⇒ Q → P ⇒ R → P ⇒ (×-poset Q R)
--[[[
⟨_,_⟩ {P} {Q} {R} f g = record
  { fun = λ p → ( |f| p , |g| p )
  ; monotone = λ {p₁} {p₂} p₁≤p₂ → _⇒_.monotone f p₁≤p₂ , _⇒_.monotone g p₁≤p₂
  }
  where
    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q
    |R| = Preorder.Carrier R

    |f| : |P| → |Q|
    |f| = _⇒_.fun f

    |g| : |P| → |R|
    |g| = _⇒_.fun g
--]]]

π₁ : {P Q : Preorder l0 l0 l0} → (×-poset P Q) ⇒ P
--[[[
π₁ {P} {Q} = record
  { fun = fun
  ; monotone = monotone
  }
  where
    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q

    fun : |P| × |Q| → |P|
    fun = proj₁

    monotone : (Preorder._≤_ (×-poset P Q)) =[ fun ]⇒ (Preorder._≤_ P)
    monotone {p₁ , q₁} {p₂ , q₂} (p₁≤p₂ , q₁≤q₂) = p₁≤p₂ 
--]]]

π₂ : {P Q : Preorder l0 l0 l0} → (×-poset P Q) ⇒ Q
--[[[
π₂ {P} {Q} = record
  { fun = fun
  ; monotone = monotone
  }
  where
    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q

    fun : |P| × |Q| → |Q|
    fun = proj₂

    monotone : (Preorder._≤_ (×-poset P Q)) =[ fun ]⇒ (Preorder._≤_ Q)
    monotone {p₁ , q₁} {p₂ , q₂} (p₁≤p₂ , q₁≤q₂) = q₁≤q₂ 
--]]]

infixl 0 _>>_
_>>_ : {P Q R : Preorder l0 l0 l0} → P ⇒ Q → Q ⇒ R → P ⇒ R
_>>_ {P} {Q} {R} f g = g ∘ f

⇒-poset : (P Q : Preorder l0 l0 l0) → Preorder l0 l0 l0
--[[[
⇒-poset P Q =
  record
  { Carrier = P ⇒ Q
  ; isPartialOrder = leqPartialOrder
  }
  where
    |P| : Set
    |P| = Preorder.Carrier P
    _d≈_ : |P| → |P| → Set
    _d≈_ = Preorder._≈_ P
    _d≤_ : |P| → |P| → Set
    _d≤_ = Preorder._≤_ P
    
    |Q| : Set
    |Q| = Preorder.Carrier Q
    _c≈_ : |Q| → |Q| → Set
    _c≈_ = Preorder._≈_ Q
    _c≤_ : |Q| → |Q| → Set
    _c≤_ = Preorder._≤_ Q
    isPartialOrderCod : IsPartialOrder _c≈_ _c≤_
    isPartialOrderCod = Preorder.isPartialOrder Q

    _eq_ : (P ⇒ Q) → (P ⇒ Q) → Set
    f' eq g' = ∀ {v : |P|} → Preorder._≈_ Q (f v) (g v)
      where
        f = _⇒_.fun f'
        g = _⇒_.fun g'

    _leq_ : (P ⇒ Q) → (P ⇒ Q) → Set
    f' leq g' = ∀{v : |P|} → (f v) c≤ (g v) 
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

        fv≤gv : (f v) c≤ (g v)
        fv≤gv = f≤g {v}

        gv≤hv : (g v) c≤ (h v)
        gv≤hv = g≤h {v}

        trans≤ : Transitive _c≤_
        trans≤ = IsPartialOrder.trans isPartialOrderCod

    leqAntisym : Antisymmetric _eq_ _leq_
    leqAntisym {f} {g} f≤g g≤f = Preorder.antisym Q f≤g g≤f
        
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
--]]]

Λ : {P Q R : Preorder l0 l0 l0} → ((×-poset P Q) ⇒ R) → Q ⇒ (⇒-poset P R)
--[[[
Λ {P} {Q} {R} P×Q⇒R = record
  { fun = fun
  ; monotone = monotone
  }
  where
    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q
    |R| = Preorder.Carrier R

    fun : (Preorder.Carrier Q) → (P ⇒ R)
    fun q = record
      { fun = funRes
      ; monotone = monoRes
      }
      where
        funRes : |P| → |R|
        funRes p = (_⇒_.fun P×Q⇒R) (p , q)

        monoRes : (Preorder._≤_ P) =[ funRes ]⇒ (Preorder._≤_ R)
        monoRes {p₁} {p₂} p₁≤p₂ = _⇒_.monotone P×Q⇒R (p₁≤p₂ , Preorder.refl Q)

    monotone : (Preorder._≤_ Q) =[ fun ]⇒ (Preorder._≤_ (⇒-poset P R))
    monotone {q₁} {q₂} q₁≤q₂ {p} = _⇒_.monotone P×Q⇒R (Preorder.refl P , q₁≤q₂)
--]]]

ev : {A B : Preorder l0 l0 l0} → ((×-poset A (⇒-poset A B)) ⇒ B)
--[[[
ev {A} {B} = 
  record
  { fun = fun
  ; monotone = λ {x} {y} → monotone {x} {y}
  }
  where
    |A| = Preorder.Carrier A
    |B| = Preorder.Carrier B

    fun : (|A| × (A ⇒ B)) → |B|
    fun (a , f) = _⇒_.fun f a

    monotone : (Preorder._≤_ (×-poset A (⇒-poset A B))) =[ fun ]⇒ (Preorder._≤_ B)
    monotone {a₁ , f₁} {a₂ , f₂} (a₁≤a₂ , f₁≤f₂) = 
      begin
        |f₁| a₁ ≤⟨ _⇒_.monotone f₁ a₁≤a₂ ⟩
        |f₁| a₂ ≤⟨ f₁≤f₂ ⟩
        |f₂| a₂
       ∎ 
      where
        open import Relation.Binary.PartialOrderReasoning B
        |f₁| = _⇒_.fun f₁
        |f₂| = _⇒_.fun f₂
--]]]

-- sum (coproduct) property
[[+]] : {A B C : Preorder l0 l0 l0} → (×-poset (⇒-poset A C) (⇒-poset B C)) ⇒ (⇒-poset (⊎-poset {l0} {l0} {l0} {l0} {l0} {l0} A B) C)
[[+]] {A} {B} {C} =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    poset-A⊎B = ⊎-poset {l0} {l0} {l0} {l0} {l0} {l0} A B

    fun : (Preorder.Carrier (×-poset (⇒-poset A C) (⇒-poset B C))) → (Preorder.Carrier (⇒-poset poset-A⊎B C))
    fun (a⇒c , b⇒c) = record
      { fun = fun'
      ; monotone = monotone'
      }
      where
        fun' : (Preorder.Carrier poset-A⊎B) → (Preorder.Carrier C)
        fun' (inj₁ a) = _⇒_.fun a⇒c a
        fun' (inj₂ b) = _⇒_.fun b⇒c b
 
        monotone' : (Preorder._≤_ poset-A⊎B) =[ fun'  ]⇒ (Preorder._≤_ C)
        monotone' {inj₁ _} {inj₂ _} (₁∼₂ ())
        monotone' {inj₁ a₁} {inj₁ a₂} (₁∼₁ a₁≤a₂) = _⇒_.monotone a⇒c a₁≤a₂
        monotone' {inj₂ b₁} {inj₂ b₂} (₂∼₂ b₁≤b₂) = _⇒_.monotone b⇒c b₁≤b₂

    monotone : (Preorder._≤_ (×-poset (⇒-poset A C) (⇒-poset B C))) =[ fun ]⇒ (Preorder._≤_ (⇒-poset poset-A⊎B C))
    monotone {a⇒c₁ , b⇒c₁} {a⇒c₂ , b⇒c₂} (a⇒c₁≤a⇒c₂ , b⇒c₁≤b⇒c₂) {inj₁ a} = a⇒c₁≤a⇒c₂ {a}
    monotone {a⇒c₁ , b⇒c₁} {a⇒c₂ , b⇒c₂} (a⇒c₁≤a⇒c₂ , b⇒c₁≤b⇒c₂) {inj₂ b} = b⇒c₁≤b⇒c₂ {b}