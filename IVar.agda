open import Relation.Binary renaming (_⇒_ to _Implies_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.Lattice
open import Util
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.All
open import Data.List.Any
open import Data.Product

module IVar (E : StrictTotalOrder l0 l0 l0) where

|E| = StrictTotalOrder.Carrier E
_<E_ = StrictTotalOrder._<_ E
_≈E_ = StrictTotalOrder._≈_ E
≈E-setoid = StrictTotalOrder.Eq.setoid E
trans-≈E = StrictTotalOrder.Eq.trans E

--data IsIVar : List |E| → Set where
--  []-IVar : IsIVar []
--  ∷-IVar : (hd : |E|) → (tl : List |E|) → (All (λ · → hd <E ·) tl) → (IsIVar tl) → IsIVar (hd ∷ tl)

--⌈⌉-Ty : Set
--⌈⌉-Ty = Σ[ l ∈ List |E| ] (IsIVar l)

open import DiscreteDelta E
open import FreeSemilattice (deltaPoset) public

⌈⌉-semilat : BoundedJoinSemilattice l0 l0 l0
⌈⌉-semilat = FP-BJS 

⌈⌉-poset : Poset l0 l0 l0
⌈⌉-poset = BoundedJoinSemilattice.poset ⌈⌉-semilat

⌈⌉-Ty : Set 
⌈⌉-Ty = BoundedJoinSemilattice.Carrier ⌈⌉-semilat
{-
⌈⌉-poset : Poset l0 l0 l0
⌈⌉-poset = 
  record
  { Carrier = ⌈⌉-Ty
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

    _≤'_ : ⌈⌉-Ty → ⌈⌉-Ty → Set
    (l₁ , _) ≤' (l₂ , _) = All (λ · → Any (· ≈E_) l₂) l₁

    _≈'_ : ⌈⌉-Ty → ⌈⌉-Ty → Set
    a ≈' b = (a ≤' b) × (b ≤' a)

    reflexive' : _≈'_ Implies _≤'_
    reflexive' (l , _) = l

    refl' : Reflexive _≤'_
    refl' {l , _} = tabulateAll f
      where
        f : ∀ {x} → x ∈ l → Any (x ≈E_) l
        f {x} x∈l = mapAny p x∈l
          where
            p : ∀ {y} → x ≡ y → x ≈E y
            p {e} PE.refl = StrictTotalOrder.Eq.refl E      
    
    trans-≤' : Transitive _≤'_
    trans-≤' {l1 , _} {l2 , _} {l3 , _} d1≤d2 d2≤d3 =
      LAll.tabulate tab
      where
        open import Data.List.Membership.Propositional
        open import Data.List.All as LAll
        open import Data.List.Any as LAny

        tab : {x : |E|} → x ∈ l1 → Any (x ≈E_) l3
        tab {x} x∈l1 = anyEliminate l2 elim (LAll.lookup d1≤d2 x∈l1)
          where
            elim : AnyEliminator {ℓQ = l0} |E| (Any (x ≈E_) l3) (x ≈E_) l2
            elim a f x≈a a∈l2 = LAny.map (λ a≈· → trans-≈E x≈a a≈·) (LAll.lookup d2≤d3 a∈l2)        

    trans-≈' : Transitive _≈'_
    trans-≈' {d1} {d2} {d3} (l1∼l2 , l2∼l1) (l2∼l3 , l3∼l2) = 
      trans-≤' {d1} {d2} {d3} l1∼l2 l2∼l3 , trans-≤' {d3} {d2} {d1} l3∼l2 l2∼l1 

    sym-≈' : Symmetric _≈'_
    sym-≈' (d1∼d2 , d2∼d1) = (d2∼d1 , d1∼d2)

    antisym-≤' : Antisymmetric _≈'_ _≤'_
    antisym-≤' a≤b b≤a = a≤b , b≤a
-}


{-
⌈⌉-semilat : BoundedJoinSemilattice l0 l0 l0
⌈⌉-semilat = record
  { Carrier = ⌈⌉-Ty
  ; _≤_ = _≤'_
  ; _≈_ = _≈'_ 
  ; _∨_ = {!!} -- _∨'_
  ; ⊥ = ⊥'
  ; isBoundedJoinSemilattice = {!!}
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
    open import Data.List.Membership.Setoid (≈E-setoid) renaming (_∈_ to _∈E_) 
    open import Data.Sum
    open import Function.Equivalence
    _≤'_ : ⌈⌉-Ty → ⌈⌉-Ty → Set
    (l₁ , _) ≤' (l₂ , _) = All (λ · → Any (· ≈E_) l₂) l₁

    _≈'_ : ⌈⌉-Ty → ⌈⌉-Ty → Set
    a ≈' b = (a ≤' b) × (b ≤' a)

    ⊥' : ⌈⌉-Ty
    ⊥' = [] , []-IVar

    _∨'_ : (a : ⌈⌉-Ty) → (b : ⌈⌉-Ty) → Σ[ c ∈ ⌈⌉-Ty ] ∀ (x : |E|) → ((x ∈E proj₁ a) ⊎ (x ∈E proj₁ b)) ⇔ (x ∈E proj₁ c) 
    ([] , []-IVar) ∨' ([] , []-IVar) = ([] , []-IVar) , {!(equivalence (x→ x) !}
      where
        x→ : (x : |E|) → ((x ∈E []) ⊎ (x ∈E [])) → (x ∈E [])
        x→ x (inj₁ x∈[]) = x∈[]
        x→ x (inj₂ x∈[]) = x∈[]

        x← : (x : |E|) → (x ∈E []) → ((x ∈E []) ⊎ (x ∈E []))
        x← x x∈[] = inj₁ x∈[]

        sameElements : (x : |E|) → ((x ∈E []) ⊎ (x ∈E [])) ⇔ (x ∈E [])
        sameElements x = ?
    ([] , []-IVar) ∨' b@(_ ∷ _ , _) = b , {!!}
    a@(_ ∷ _ , _) ∨' ([] , []-IVar) = a , {!!}
    (ha ∷ ta , ∷-IVar ha ta mina ita) ∨' (hb ∷ tb , ∷-IVar hb tb minb itb) with StrictTotalOrder.compare E ha hb
    (ha ∷ ta , ∷-IVar ha ta mina ita) ∨' (hb ∷ tb , ∷-IVar hb tb minb itb) | tri< ha<hb _ _ = 
      {!!}
    (ha ∷ ta , ∷-IVar ha ta mina ita) ∨' (hb ∷ tb , ∷-IVar hb tb minb itb) | tri≈ _ ha≈hb _ = 
      {!!}
    (ha ∷ ta , ∷-IVar ha ta mina ita) ∨' (hb ∷ tb , ∷-IVar hb tb minb itb) | tri> _ _ hb<ha = 
      {!!}
  

    reflexive' : _≈'_ Implies _≤'_
    reflexive' (l , _) = l

    refl' : Reflexive _≤'_
    refl' {l , _} = tabulateAll f
      where
        f : ∀ {x} → x ∈ l → Any (x ≈E_) l
        f {x} x∈l = mapAny p x∈l
          where
            p : ∀ {y} → x ≡ y → x ≈E y
            p {e} PE.refl = StrictTotalOrder.Eq.refl E      
    
    trans-≤' : Transitive _≤'_
    trans-≤' {l1 , _} {l2 , _} {l3 , _} d1≤d2 d2≤d3 =
      LAll.tabulate tab
      where
        open import Data.List.Membership.Propositional
        open import Data.List.All as LAll
        open import Data.List.Any as LAny

        tab : {x : |E|} → x ∈ l1 → Any (x ≈E_) l3
        tab {x} x∈l1 = anyEliminate l2 elim (LAll.lookup d1≤d2 x∈l1)
          where
            elim : AnyEliminator {ℓQ = l0} |E| (Any (x ≈E_) l3) (x ≈E_) l2
            elim a f x≈a a∈l2 = LAny.map (λ a≈· → trans-≈E x≈a a≈·) (LAll.lookup d2≤d3 a∈l2)        

    trans-≈' : Transitive _≈'_
    trans-≈' {d1} {d2} {d3} (l1∼l2 , l2∼l1) (l2∼l3 , l3∼l2) = 
      trans-≤' {d1} {d2} {d3} l1∼l2 l2∼l3 , trans-≤' {d3} {d2} {d1} l3∼l2 l2∼l1 

    sym-≈' : Symmetric _≈'_
    sym-≈' (d1∼d2 , d2∼d1) = (d2∼d1 , d1∼d2)

    antisym-≤' : Antisymmetric _≈'_ _≤'_
    antisym-≤' a≤b b≤a = a≤b , b≤a

⌈⌉-poset : Poset l0 l0 l0
⌈⌉-poset = BoundedJoinSemilattice.poset ⌈⌉-semilat 
-}
