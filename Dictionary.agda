open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Lattice
open import Util
open import Data.List
open import Data.List.All
open import Data.Product
open import Relation.Nullary
open import Function as F using (_$_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

module Dictionary where


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

▹-poset : (T₀ : StrictTotalOrder l0 l0 l0) → (V : BoundedJoinSemilattice l0 l0 l0) → Poset l0 l0 l0
▹-poset T₀ V = 
  record
  { Carrier = Carrier'
  ; _≤_ = _≤'_ 
  ; _≈_ = _≈'_
  ; isPartialOrder = record
    { isPreorder = record
      { reflexive = λ {x} {y} → reflexive' {x} {y}
      ; trans = λ {x} {y} {z} → trans-≤' {x} {y} {z}
      ; isEquivalence = record
        { trans = λ {x} {y} {z} → trans-≈' {x} {y} {z}
        ; refl = λ {x} → refl' {x} , refl' {x}
        ; sym = λ {x} {y} → sym-≈' {x} {y}
        }
      }
      ; antisym = λ {x} {y} → antisym-≤' {x} {y}
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
    
    _≤'_ : Carrier' → Carrier' → Set
    (l₁ , _) ≤' (l₂ , _) = All (λ e₁ → Any (λ e₂ → e₁ ≤e e₂) l₂) l₁

    _≈'_ : Carrier' → Carrier' → Set
    i ≈' j = (i ≤' j) × (j ≤' i)

    reflexive' : _≈'_ Implies _≤'_
    reflexive' (x , _) = x

    refl' : Reflexive _≤'_
    refl' {l , _} = tabulateAll f 
      where
        f : ∀ {x} → x ∈ l → Any (x ≤e_) l
        f {x} x∈l = mapAny p x∈l
          where
            p : ∀ {y} → x ≡ y → x ≤e y
            p {l , d} PE.refl = StrictTotalOrder.Eq.refl T₀ , BoundedJoinSemilattice.refl V

    trans-≤' : Transitive _≤'_
    trans-≤' {l1 , _} {l2 , _} {l3 , _} d1≤d2 d2≤d3 =
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
      trans-≤' {d1} {d2} {d3} l1∼l2 l2∼l3 , trans-≤' {d3} {d2} {d1} l3∼l2 l2∼l1 

    sym-≈' : Symmetric _≈'_
    sym-≈' (d1∼d2 , d2∼d1) = (d2∼d1 , d1∼d2)

    antisym-≤' : Antisymmetric _≈'_ _≤'_
    antisym-≤' a≤b b≤a = a≤b , b≤a
