module Preorders where

open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum
open import Data.Sum.Relation.Pointwise
open import Data.List
open import Data.List.All
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.Lattice
open import Function as F using (_$_)
open import Level

open import Util
open import RelationalStructures
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


⊎-preorder0 : Preorder l0 l0 l0 → Preorder l0 l0 l0 → Preorder l0 l0 l0
⊎-preorder0 = ⊎-preorder {l0} {l0} {l0} {l0} {l0} {l0}

_⟨+⟩_ : {P Q R S : Preorder l0 l0 l0} → P ⇒ R → Q ⇒ S → (⊎-preorder P Q) ⇒ (⊎-preorder R S)
_⟨+⟩_ {P} {Q} {R} {S} f g = record
  { fun = fun
  ; monotone = monotone
  }
  where
    open Preorder
    |P| = Carrier P
    |Q| = Carrier Q
    |R| = Carrier R
    |S| = Carrier S

    fun : (|P| ⊎ |Q|) → (|R| ⊎ |S|)
    fun (inj₁ p) = inj₁ $ (_⇒_.fun f) p
    fun (inj₂ q) = inj₂ $ (_⇒_.fun g) q

    monotone : (_∼_ (⊎-preorder P Q)) =[ fun ]⇒ (_∼_ (⊎-preorder R S))
    monotone {inj₁ p₁} {inj₁ p₂} (₁∼₁ p₁∼p₂) = ₁∼₁ (_⇒_.monotone f p₁∼p₂)  
    monotone {inj₁ p₁} {inj₂ q₂} (₁∼₂ ())
    monotone {inj₂ q₁} {inj₁ p₂} ()
    monotone {inj₂ q₁} {inj₂ q₂} (₂∼₂ q₁∼q₂) = ₂∼₂ (_⇒_.monotone g q₁∼q₂)

_⟨×⟩_ : {P Q R S : Preorder l0 l0 l0} → P ⇒ Q → R ⇒ S → (×-preorder P R) ⇒ (×-preorder Q S)
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

    monotone : _∼_ (×-preorder P R) =[ fun ]⇒ _∼_ (×-preorder Q S)
    monotone {p₁ , r₁} {p₂ , r₂} (p₁≤p₂ , r₁≤r₂) = (_⇒_.monotone f p₁≤p₂ , _⇒_.monotone g r₁≤r₂)
--]]]

⟨_,_⟩ : {P Q R : Preorder l0 l0 l0} → P ⇒ Q → P ⇒ R → P ⇒ (×-preorder Q R)
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

π₁ : {P Q : Preorder l0 l0 l0} → (×-preorder P Q) ⇒ P
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

    monotone : (Preorder._∼_ (×-preorder P Q)) =[ fun ]⇒ (Preorder._∼_ P)
    monotone {p₁ , q₁} {p₂ , q₂} (p₁≤p₂ , q₁≤q₂) = p₁≤p₂ 
--]]]

π₂ : {P Q : Preorder l0 l0 l0} → (×-preorder P Q) ⇒ Q
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

    monotone : (Preorder._∼_ (×-preorder P Q)) =[ fun ]⇒ (Preorder._∼_ Q)
    monotone {p₁ , q₁} {p₂ , q₂} (p₁≤p₂ , q₁≤q₂) = q₁≤q₂ 
--]]]

infixl 0 _>>_
_>>_ : {P Q R : Preorder l0 l0 l0} → P ⇒ Q → Q ⇒ R → P ⇒ R
_>>_ {P} {Q} {R} f g = g ∘ f


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

Λ : {P Q R : Preorder l0 l0 l0} → ((×-preorder P Q) ⇒ R) → Q ⇒ (⇒-preorder P R)
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

        monoRes : (Preorder._∼_ P) =[ funRes ]⇒ (Preorder._∼_ R)
        monoRes {p₁} {p₂} p₁≤p₂ = _⇒_.monotone P×Q⇒R (p₁≤p₂ , Preorder.refl Q)

    monotone : (Preorder._∼_ Q) =[ fun ]⇒ (Preorder._∼_ (⇒-preorder P R))
    monotone {q₁} {q₂} q₁≤q₂ {p} = _⇒_.monotone P×Q⇒R (Preorder.refl P , q₁≤q₂)
--]]]

ev : {A B : Preorder l0 l0 l0} → ((×-preorder A (⇒-preorder A B)) ⇒ B)
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

    monotone : (Preorder._∼_ (×-preorder A (⇒-preorder A B))) =[ fun ]⇒ (Preorder._∼_ B)
    monotone {a₁ , f₁} {a₂ , f₂} (a₁≤a₂ , f₁≤f₂) = 
      begin
        |f₁| a₁ ∼⟨ _⇒_.monotone f₁ a₁≤a₂ ⟩
        |f₁| a₂ ∼⟨ f₁≤f₂ ⟩
        |f₂| a₂
       ∎ 
      where
        open import Relation.Binary.PreorderReasoning B
        |f₁| = _⇒_.fun f₁
        |f₂| = _⇒_.fun f₂
--]]]

-- sum (coproduct) property
[[+]] : {A B C : Preorder l0 l0 l0} → (×-preorder (⇒-preorder A C) (⇒-preorder B C)) ⇒ (⇒-preorder (⊎-preorder0 A B) C)
[[+]] {A} {B} {C} =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    preorder-A⊎B = ⊎-preorder0 A B

    fun : (Preorder.Carrier (×-preorder (⇒-preorder A C) (⇒-preorder B C))) → (Preorder.Carrier (⇒-preorder preorder-A⊎B C))
    fun (a⇒c , b⇒c) = record
      { fun = fun'
      ; monotone = monotone'
      }
      where
        fun' : (Preorder.Carrier preorder-A⊎B) → (Preorder.Carrier C)
        fun' (inj₁ a) = _⇒_.fun a⇒c a
        fun' (inj₂ b) = _⇒_.fun b⇒c b
 
        monotone' : (Preorder._∼_ preorder-A⊎B) =[ fun'  ]⇒ (Preorder._∼_ C)
        monotone' {inj₁ _} {inj₂ _} (₁∼₂ ())
        monotone' {inj₁ a₁} {inj₁ a₂} (₁∼₁ a₁≤a₂) = _⇒_.monotone a⇒c a₁≤a₂
        monotone' {inj₂ b₁} {inj₂ b₂} (₂∼₂ b₁≤b₂) = _⇒_.monotone b⇒c b₁≤b₂

    monotone : (Preorder._∼_ (×-preorder (⇒-preorder A C) (⇒-preorder B C))) =[ fun ]⇒ (Preorder._∼_ (⇒-preorder preorder-A⊎B C))
    monotone {a⇒c₁ , b⇒c₁} {a⇒c₂ , b⇒c₂} (a⇒c₁≤a⇒c₂ , b⇒c₁≤b⇒c₂) {inj₁ a} = a⇒c₁≤a⇒c₂ {a}
    monotone {a⇒c₁ , b⇒c₁} {a⇒c₂ , b⇒c₂} (a⇒c₁≤a⇒c₂ , b⇒c₁≤b⇒c₂) {inj₂ b} = b⇒c₁≤b⇒c₂ {b}

κ₁ : {P Q : Preorder l0 l0 l0} → P ⇒ (⊎-preorder P Q)
κ₁ {P} {Q} =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    open Preorder
    fun : (Carrier P) → (Carrier (⊎-preorder P Q))
    fun p = inj₁ p

    monotone : (_∼_ P) =[ fun ]⇒ (_∼_ (⊎-preorder P Q))
    monotone {p₁} {p₂} p₁∼p₂ = ₁∼₁ p₁∼p₂

κ₂ : {P Q : Preorder l0 l0 l0} → Q ⇒ (⊎-preorder P Q)
κ₂ {P} {Q} =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    open Preorder
    fun : (Carrier Q) → (Carrier (⊎-preorder P Q))
    fun q = inj₂ q

    monotone : (_∼_ Q) =[ fun ]⇒ (_∼_ (⊎-preorder P Q))
    monotone {p₁} {p₂} p₁∼p₂ = ₂∼₂ p₁∼p₂

precomp : {P Q R : Preorder l0 l0 l0} → (P ⇒ Q) → (⇒-preorder Q R) ⇒ (⇒-preorder P R)
precomp {P} {Q} {R} (record {fun = p→q ; monotone = p→q-monotone}) =
  record
  { fun = fun
  ; monotone = λ {f₁} {f₂} → monotone {f₁} {f₂}
  }
  where
    open Preorder
    |P| = Carrier P
    |Q| = Carrier Q
    |R| = Carrier R
    
    fun : (Q ⇒ R) → (P ⇒ R)
    fun (record {fun = q→r ; monotone = q→r-monotone}) =
      record
      { fun = p→r
      ; monotone = p→r-monotone
      }
      where
        p→r : |P| → |R|
        p→r p = q→r (p→q p)

        p→r-monotone : (_∼_ P) =[ p→r ]⇒ (_∼_ R)
        p→r-monotone {p₁} {p₂} p₁≤p₂ = q→r-monotone (p→q-monotone p₁≤p₂) 

    monotone : (_∼_ $ ⇒-preorder Q R) =[ fun ]⇒ (_∼_ $ ⇒-preorder P R)
    monotone {f₁} {f₂} f₁≤f₂ {p} = f₁≤f₂


module _ (K : StrictTotalOrder l0 l0 l0) (V : BoundedJoinSemilattice l0 l0 l0) where
  private
   |K| = StrictTotalOrder.Carrier K
   |V| = BoundedJoinSemilattice.Carrier V
   _<_ = StrictTotalOrder._<_ K
   _≈k_ = StrictTotalOrder.Eq._≈_ K
   _≤v_ = BoundedJoinSemilattice._≤_ V
   _≈v_ = BoundedJoinSemilattice._≈_ V
   ⊥v = BoundedJoinSemilattice.⊥ V

  data IsDict : List (|K| × |V|) → Set where
    []-Dict : IsDict []
    ∷-Dict : (hd : |K| × |V|) → (tl : List (|K| × |V|)) → (All (λ · → proj₁ hd < proj₁ ·) tl) → 
                ¬ (proj₂ hd ≈v ⊥v) → (IsDict tl) → IsDict (hd ∷ tl) 

_▹_ : (K : StrictTotalOrder l0 l0 l0) → (V : BoundedJoinSemilattice l0 l0 l0) → Set
K ▹ V = Σ[ l ∈ (List $ |K| × |V|) ] IsDict K V l
  where
    |K| = StrictTotalOrder.Carrier K
    |V| = BoundedJoinSemilattice.Carrier V

▹-preorder : (T₀ : StrictTotalOrder l0 l0 l0) → (T₁ : Preorder l0 l0 l0) → 
             (StrictTotalOrder.Carrier T₀ ≡ Preorder.Carrier T₁) →  
             (V : BoundedJoinSemilattice l0 l0 l0) → 
             Preorder l0 l0 l0

▹-preorder T₀ T₁ PE.refl V = 
  record
  { Carrier = Carrier'
  ; _∼_ = _∼'_ 
  ; _≈_ = _≈'_
  ; isPreorder = record 
    { reflexive = λ {x} {y} → reflexive' {x} {y}
    ; trans = λ {x} {y} {z} → trans-∼' {x} {y} {z}
    ; isEquivalence = record
      { trans = λ {x} {y} {z} → trans-≈' {x} {y} {z}
      ; refl = λ {x} → refl' {x} , refl' {x}
      ; sym = λ {x} {y} → sym-≈' {x} {y}
      }
    }
  } 
  where
    open import Data.List.Any renaming (map to mapAny)
    open import Data.List.All renaming (map to mapAll ; tabulate to tabulateAll)
    open import Data.List.Membership.Propositional
    open import Relation.Binary renaming (_⇒_ to _Implies_)
 
    |K| = StrictTotalOrder.Carrier T₀
    |V| = BoundedJoinSemilattice.Carrier V
    _<_ = StrictTotalOrder._<_ T₀
    _≈k_ = StrictTotalOrder.Eq._≈_ T₀
    _≤v_ = BoundedJoinSemilattice._≤_ V
    _≈v_ = BoundedJoinSemilattice._≈_ V
    ⊥v = BoundedJoinSemilattice.⊥ V
    
    |E| = |K| × |V|
    
    Carrier' : Set
    Carrier' = T₀ ▹ V
    
    --entry comparison 
    _≤e_ : |E| → |E| → Set
    (k₁ , v₁) ≤e (k₂ , v₂) = (k₁ ≈k k₂) × (v₁ ≤v v₂) 
    
    trans-≤e : Transitive _≤e_
    trans-≤e (k1≈k2 , v1≤v2) (k2≈k3 , v2≤v3) = 
      StrictTotalOrder.Eq.trans T₀ k1≈k2 k2≈k3 , BoundedJoinSemilattice.trans V v1≤v2 v2≤v3
    
    _∼'_ : Carrier' → Carrier' → Set
    (l₁ , _) ∼' (l₂ , _) = All (λ e₁ → Any (λ e₂ → e₁ ≤e e₂) l₂) l₁

    _≈'_ : Carrier' → Carrier' → Set
    i ≈' j = (i ∼' j) × (j ∼' i)

    reflexive' : _≈'_ Implies _∼'_
    reflexive' (x , _) = x

    refl' : Reflexive _∼'_
    refl' {l , _} = tabulateAll f 
      where
        f : ∀ {x} → x ∈ l → Any (x ≤e_) l
        f {x} x∈l = mapAny p x∈l
          where
            p : ∀ {y} → x ≡ y → x ≤e y
            p {l , d} PE.refl = StrictTotalOrder.Eq.refl T₀ , BoundedJoinSemilattice.refl V

    trans-∼' : Transitive _∼'_
    trans-∼' {l1 , _} {l2 , _} {l3 , _} d1≤d2 d2≤d3 =
      LAll.tabulate tab
      where
        open import Data.List.Membership.Propositional
        open import Data.List.All as LAll
        open import Data.List.Any as LAny

        tab : {x : |E|} → x ∈ l1 → Any (x ≤e_) l3
        tab {x} x∈l1 = anyEliminate l2 elim (LAll.lookup d1≤d2 x∈l1)
          where
            elim : AnyEliminator {ℓQ = l0} |E| (Any (x ≤e_) l3) (x ≤e_) l2
            elim a f x≤a a∈l2 = LAny.map (λ a≤· → trans-≤e x≤a a≤·) (LAll.lookup d2≤d3 a∈l2)

    trans-≈' : Transitive _≈'_
    trans-≈' {d1} {d2} {d3} (l1∼l2 , l2∼l1) (l2∼l3 , l3∼l2) = 
      trans-∼' {d1} {d2} {d3} l1∼l2 l2∼l3 , trans-∼' {d3} {d2} {d1} l3∼l2 l2∼l1 

    sym-≈' : Symmetric _≈'_
    sym-≈' (d1∼d2 , d2∼d1) = (d2∼d1 , d1∼d2)
