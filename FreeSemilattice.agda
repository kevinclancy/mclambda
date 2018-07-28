open import Function using (_$_)
open import Data.Empty
open import Data.List
open import Data.List.All as LA
open import Data.List.Any as LAny
open import Data.List.Any.Properties as LAP
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE
open import RelationalStructures
open import Util

module FreeSemilattice (P : DeltaPoset0) where

open DeltaPoset0 P renaming (trans to tran)

data IsFreeList {A : Set l0} (_<_ : Rel A l0) (_⊑_ : Rel A l0) : List A → Set l1 where
  []-Free : IsFreeList _<_ _⊑_ []
  ∷-Free : (hd : A) → (tl : List A) → (All (hd <_) tl) → ¬ (Any (λ x → (hd ⊑ x) ⊎ (x ⊑ hd)) tl) → 
            (IsFreeList _<_ _⊑_ tl) → IsFreeList _<_ _⊑_ (hd ∷ tl) 

Carrier-FP : Set₁
Carrier-FP = Σ[ x ∈ List Carrier ] (IsFreeList _<_ _⊑_ x)

data _≤_ : Carrier-FP → Carrier-FP → Set₁ where
  []-≤ : {cfp : Carrier-FP} → ([] , []-Free) ≤ cfp  
  cmp-≤ : {h1 h2 : Carrier} {t1 t2 : List Carrier} → (ft1 : IsFreeList _<_ _⊑_ t1) →
          (f1 : IsFreeList _<_ _⊑_ (h1 ∷ t1)) →
          (f2 : IsFreeList _<_ _⊑_ (h2 ∷ t2)) →
          h1 ⊑ h2 →
          (t1 , ft1) ≤ (h2 ∷ t2 , f2) →
          (h1 ∷ t1 , f1) ≤ (h2 ∷ t2 , f2)
  skip-≤ : {h1 h2 : Carrier} {t1 t2 : List Carrier} → 
            (f1 : IsFreeList _<_ _⊑_ (h1 ∷ t1)) → 
            (ft2 : IsFreeList _<_ _⊑_ t2) → 
            (f2 : IsFreeList _<_ _⊑_ (h2 ∷ t2)) →
            (h2 < h1) → (h1 ∥ h2) → (h1 ∷ t1 , f1) ≤ (t2 , ft2) →
            (h1 ∷ t1 , f1) ≤ (h2 ∷ t2 , f2)

_<=_ : (l1 l2 : Carrier-FP) → Set
(l1 , f1) <= (l2 , f2) = All (λ x → Any (x ⊑_) l2) l1

≤→<= : {l1 l2 : Carrier-FP} → (l1 ≤ l2) → (l1 <= l2)
≤→<= {.([] , []-Free)} {l2} []-≤ = 
  []
≤→<= {h1 ∷ t1 , f1} {h2 ∷ t2 , f2} (cmp-≤ ft1 .f1 .f2 h1⊑h2 t1≤l2) = 
  (here h1⊑h2) ∷ ≤→<= t1≤l2
≤→<= {h1 ∷ t1 , f1} {h2 ∷ t2 , f2} (skip-≤ .f1 ft2 f2 h2<h1 h1∥h2 l1≤t2) = 
  LA.map (λ x⊑t2 → there x⊑t2) (≤→<= l1≤t2)

<=→≤ : {l1 l2 : Carrier-FP} → (l1 <= l2) → (l1 ≤ l2)
<=→≤ {[] , []-Free} {l2 , f2} [] = 
  []-≤
<=→≤ {h1 ∷ t1 , f1@(∷-Free .h1 .t1 min1 incomp1 ft1)} {[] , []-Free} (h1⊑l2 ∷ t1<=l2) =
  ⊥-elim $ ¬Any[] h1⊑l2
<=→≤ {h1 ∷ t1 , f1@(∷-Free .h1 .t1 min1 incomp1 ft1)} {l2@(h2 ∷ t2) , f2@(∷-Free _ _ _ _ ft2)} (h1⊑l2 ∷ t1<=l2) 
  with (<=→≤ {t1 , ft1} {h2 ∷ t2 , f2} t1<=l2) 
<=→≤ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {l2@(h2 ∷ t2) , f2} (here (h1⊑h2) ∷ t1<=l2) | t1≤l2 =
  cmp-≤ ft1 f1 f2 h1⊑h2 t1≤l2
<=→≤ {h1 ∷ t1 , ∷-Free .h1 .t1 _ _ _} {h2 ∷ t2 , ∷-Free .h2 .t2 min2 incomp2 _} h1≤l2@(there h1⊑t2 ∷ t1<=l2) | t1≤l2 with h1 ∦? h2
<=→≤ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ _ _ _)} t1≤l2@(there h1⊑t2 ∷ t1<=l2) | t1≤l2 | l⊑r h1⊑h2 ¬h2⊑h1 =
   cmp-≤ ft1 f1 f2 h1⊑h2 t1≤l2 
<=→≤ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ _ incomp2 _)} t1≤l2@(there h1⊑t2 ∷ t1<=l2) | t1≤l2 | r⊑l ¬h1⊑h2 h2⊑h1 =
 let
    eliminator : AnyEliminator Carrier ⊥ (h1 ⊑_) t2
    eliminator a f h1⊑a a∈t2 = incomp2 $ f (λ x → h2 ∦ x) (inj₁ $ transitive⊑ h2⊑h1 h1⊑a)
  in
  ⊥-elim $ anyEliminate t2 eliminator h1⊑t2
<=→≤ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ _ _ _)} t1≤l2@(there h1⊑t2 ∷ t1<=l2) | t1≤l2 | l≡r h1≡h2 =
  cmp-≤ ft1 f1 f2 (reflexive h1≡h2) t1≤l2
<=→≤ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ _ _ _)} t1≤l2@(there h1⊑t2 ∷ t1<=l2) | t1≤l2 | l∥r h1∥h2 with compare h1 h2
<=→≤ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ min2 incomp2 _)} t1≤l2@(there h1⊑t2 ∷ t1<=l2) | t1≤l2 | l∥r h1∥h2 | tri< h1<h2 _ _ =
  let
    eliminator : AnyEliminator Carrier ⊥ (h1 ⊑_) t2
    eliminator a f h1⊑a a∈t2 = (unimodality h1<h2 (LA.lookup min2 a∈t2) (∦-refl h1) h1∥h2) (inj₁ h1⊑a)
  in
  ⊥-elim $ anyEliminate t2 eliminator h1⊑t2
<=→≤ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ min2 incomp2 _)} t1≤l2@(there h1⊑t2 ∷ t1<=l2) | t1≤l2 | l∥r h1∥h2 | tri≈ _ h1≡h2@PE.refl _ =
  ⊥-elim $ h1∥h2 (∦-refl h1) 
<=→≤ {h1 ∷ t1 , f1@(∷-Free _ _ min1 _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ min2 incomp2 ft2)} l1≤l2@(there h1⊑t2 ∷ t1<=l2) | t1≤l2 | l∥r h1∥h2 | tri> _ _ h2<h1 =
  skip-≤ f1 ft2 f2 h2<h1 h1∥h2 (<=→≤ l1≤t2)
  where
    p : Any (h1 ⊑_) t2
    p = h1⊑t2

    q : {x : Carrier} → x ∈ t1 → Any (x ⊑_) t2
    q {x} x∈t1 with (LA.lookup l1≤l2 (there x∈t1))
    q {x} x∈t1 | (here x⊑h2) = ⊥-elim $ (unimodality h2<h1 h1<x (∦-refl h2) (∥-sym h1∥h2)) (inj₂ x⊑h2)
      where
        h1<x = LA.lookup min1 x∈t1
    q {x} x∈t1 | (there x⊑t2) = x⊑t2

    l1≤t2 : All (λ x → Any (x ⊑_) t2) (h1 ∷ t1)
    l1≤t2 = p ∷ (LA.tabulate q)
  
_∨_ : List Carrier → List Carrier → List Carrier
[] ∨ t2 = t2
(h1 ∷ t1) ∨ [] = h1 ∷ t1
(h1 ∷ t1) ∨ (h2 ∷ t2) with h1 ∦? h2
(h1 ∷ t1) ∨ (h2 ∷ t2) | l⊑r h1⊑h2 ¬h2⊑h1 = t1 ∨ (h2 ∷ t2)
(h1 ∷ t1) ∨ (h2 ∷ t2) | r⊑l ¬h1⊑h2 h2⊑h1 = (h1 ∷ t1) ∨ t2
(h1 ∷ t1) ∨ (h2 ∷ t2) | l≡r h1≡h2 = t1 ∨ (h2 ∷ t2)
(h1 ∷ t1) ∨ (h2 ∷ t2) | l∥r h1∥h2 with h1 <? h2
... | yes h1<h2 = h1 ∷ (t1 ∨ (h2 ∷ t2))    
... | no ¬h1<h2 = h2 ∷ ((h1 ∷ t1) ∨ t2)

∨-All : {P : Carrier → Set} → (l1 l2 : List Carrier) → (All P l1) → (All P l2) → (All P (l1 ∨ l2))
∨-All [] l2 p1 p2 = p2
∨-All (h1 ∷ t1) [] p1 p2 = p1
∨-All (h1 ∷ t1) (h2 ∷ t2) (ph1 ∷ pt1) (ph2 ∷ pt2) with h1 ∦? h2
... | l⊑r h1⊑h2 ¬h2⊑h1 = ∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2)
... | r⊑l ¬h1⊑h2 h2⊑h1 = ∨-All (h1 ∷ t1) t2 (ph1 ∷ pt1) pt2
... | l≡r h1≡h2 = ∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2)
... | l∥r h1∥h2 with h1 <? h2
... | yes h1<h2 = ph1 ∷ (∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2))
... | no ¬h1<h2 = ph2 ∷ (∨-All (h1 ∷ t1) t2 (ph1 ∷ pt1) pt2)

∨-Any : {P : Carrier → Set} → (l1 l2 : List Carrier) → ¬ (Any P l1) → ¬ (Any P l2) → ¬ (Any P (l1 ∨ l2))
∨-Any {P} [] l2 p1 p2 = p2
∨-Any {P} (h1 ∷ t1) [] p1 p2 = p1
∨-Any {P} (h1 ∷ t1) (h2 ∷ t2) p1 p2 with (h1 ∦? h2)
... | l⊑r h1⊑h2 ¬h2⊑h1 = ∨-Any t1 (h2 ∷ t2) ¬Any-t1 p2 
    where
    ¬Any-t1 : ¬ (Any P t1)
    ¬Any-t1 any-t1 = p1 (there any-t1)
... | r⊑l ¬h1⊑h2 h2⊑h1 = ∨-Any (h1 ∷ t1) t2 p1 ¬Any-t2 
    where
    ¬Any-t2 : ¬ (Any P t2)
    ¬Any-t2 any-t2 = p2 (there any-t2)
... | l≡r h1≡h2 = ∨-Any t1 (h2 ∷ t2) ¬Any-t1 p2 
    where
    ¬Any-t1 : ¬ (Any P t1)
    ¬Any-t1 any-t1 = p1 (there any-t1)
... | l∥r h1∥h2 with h1 <? h2
... | yes h1<h2 = goal
    where 
    ¬Any-t1 : ¬ (Any P t1)
    ¬Any-t1 any-t1 = p1 (there any-t1)

    goal : ¬ (Any P (h1 ∷ t1 ∨ (h2 ∷ t2)))
    goal (here px) = p1 (here px)
    goal (there z) = ∨-Any t1 (h2 ∷ t2) ¬Any-t1 p2 z
... | no ¬h1<h2 = goal h2 (h1 ∷ t1) t2 (λ ph2 → p2 $ here ph2) p1 (λ pt2 → p2 $ there pt2) 
    where
    ¬Any-t2 : ¬ (Any P t2)
    ¬Any-t2 any-t2 = p2 (there any-t2)

    -- I have to apply h t1 and t2 outside the where clause so that the termination metric registers
    goal : (h : Carrier) → (t1 t2 : List Carrier) → ¬ (P h) → ¬ (Any P t1) → ¬ (Any P t2) →  ¬ (Any P (h ∷ t1 ∨ t2))
    goal h t1 t2 a b c (here px) = a px --p2 (here px)
    goal h t1 t2 a b c (there z) = ∨-Any t1 t2 b c z  --∨-Any (h1 ∷ t1) t2 p1 ¬Any-t2 z


∨-free : {l1 l2 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → IsFreeList _<_ _⊑_ (l1 ∨ l2)
∨-free {[]} {l2} f1 f2 = f2
∨-free {(h1 ∷ t1)} {[]} f1 f2 = f1
∨-free {(h1 ∷ t1)} {(h2 ∷ t2)} f1@(∷-Free h1 t1 min1 incomp1 ft1) f2@(∷-Free h2 t2 min2 incomp2 ft2) with h1 ∦? h2
... | l⊑r h1⊑h2 ¬h2⊑h1  = ∨-free ft1 f2 
... | r⊑l ¬h1⊑h2 h2⊑h1 = ∨-free f1 ft2
... | l≡r h1≡h2 = ∨-free ft1 f2
... | l∥r h1∥h2 with h1 <? h2
... | yes h1<h2 = ∷-Free h1 (t1 ∨ (h2 ∷ t2)) min incomp (∨-free ft1 f2) 
    where
    transitive : Transitive _<_
    transitive = IsStrictTotalOrder.trans isStrictTotalOrder 

    h1<t2 : All (h1 <_) t2
    h1<t2 = LA.map {P = h2 <_} {Q = h1 <_} (λ {x} → λ h2<x → transitive h1<h2 h2<x) min2

    min : All (h1 <_) (t1 ∨ (h2 ∷ t2))
    min = ∨-All t1 (h2 ∷ t2) min1 (h1<h2 ∷ h1<t2)  

    incomp : ¬ (Any (λ x → h1 ∦ x) (t1 ∨ (h2 ∷ t2)))
    incomp p = ∨-Any t1 (h2 ∷ t2) incomp1 h1∥h2t2 p
        where
        anyEliminator : AnyEliminator Carrier ⊥ (λ x → h1 ∦ x) t2
        anyEliminator a f p a∈t2 = unimodality h1<h2 h2<a (∦-refl h1) h1∥h2 p
            where
            h2<a : h2 < a
            h2<a = LA.lookup min2 a∈t2

        h1∥t2 : ¬ (Any (λ x → h1 ∦ x) t2)
        h1∥t2 h1∦t2 = anyEliminate t2 anyEliminator h1∦t2

        h1∥h2t2 : ¬ (Any (λ x → h1 ∦ x) (h2 ∷ t2))
        h1∥h2t2 (here h1∦h2) = h1∥h2 h1∦h2
        h1∥h2t2 (there h1∦t2) = h1∥t2 h1∦t2
... | no ¬h1<h2 = ∷-Free h2 ((h1 ∷ t1) ∨ t2) min incomp (∨-free f1 ft2)  
    where
    transitive : Transitive _<_
    transitive = IsStrictTotalOrder.trans isStrictTotalOrder 

    total : Trichotomous _≡_ _<_
    total = IsStrictTotalOrder.compare isStrictTotalOrder

    h2<h1 : h2 < h1
    h2<h1 with (total h2 h1)
    h2<h1 | tri< goal _ _ = goal
    h2<h1 | tri≈ _ h2≈h1 _ = ⊥-elim (∥⇒¬≈ (∥-sym h1∥h2) h2≈h1) 
    h2<h1 | tri> _ _ h1<h2 = ⊥-elim (¬h1<h2 h1<h2) 

    h2<t1 : All (h2 <_) t1
    h2<t1 = LA.map {P = h1 <_} {Q = h2 <_} (λ {x} → λ h1<x → transitive h2<h1 h1<x) min1

    min : All (h2 <_) ((h1 ∷ t1) ∨ t2)
    min = ∨-All (h1 ∷ t1) t2 (h2<h1 ∷ h2<t1) min2  

    incomp : ¬ (Any (λ x → h2 ∦ x) ((h1 ∷ t1) ∨ t2))
    incomp p = ∨-Any (h1 ∷ t1) t2 h2∥h1t1 incomp2 p
        where
        anyEliminator : AnyEliminator Carrier ⊥ (λ x → h2 ∦ x) t1
        anyEliminator a f p a∈t1 = unimodality h2<h1 h1<a (∦-refl h2) (∥-sym h1∥h2) p
            where
            h1<a : h1 < a
            h1<a = LA.lookup min1 a∈t1

        h2∥t1 : ¬ (Any (λ x → h2 ∦ x) t1)
        h2∥t1 h2∦t1 = anyEliminate t1 anyEliminator h2∦t1

        h2∥h1t1 : ¬ (Any (λ x → h2 ∦ x) (h1 ∷ t1))
        h2∥h1t1 (here h2∦h1) = h1∥h2 (∦-sym h2∦h1)
        h2∥h1t1 (there h2∦t1) = h2∥t1 h2∦t1

∨-lemma : {l1 l2 l3 : List Carrier} → {a : Carrier} → {f1 : IsFreeList _<_ _⊑_ l1} → {f2 : IsFreeList _<_ _⊑_ l2} → 
           {f3 : IsFreeList _<_ _⊑_ l3} → (l1 ∨ l2 ≡ l3) → (a ∈ l3) → 
           (a ∈ l1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈ l1 × a ∈ l2)

∨-lemma {[]} {[]} {.[]} {a} {f1} {f2} {f3} PE.refl a∈l3 = 
  ⊥-elim $ ¬Any[] a∈l3
∨-lemma {[]} {h2 ∷ l2} {.(h2 ∷ l2)} {a} {f1} {f2} {f3} PE.refl a∈l3 = 
  inj₂ $ inj₁ $ (a∈l3 , ¬Any[])
∨-lemma {h1 ∷ t1} {[]} {.(h1 ∷ t1)} {a} {f1} {f2} {f3} PE.refl a∈l3 = 
  inj₁ $ (a∈l3 , ¬Any[])
∨-lemma {h1 ∷ t1} {h2 ∷ t2} {_} {a} {f1} {f2} {f3} PE.refl a∈l3 with h1 ∦? h2
∨-lemma {l1@(h1 ∷ t1)} {l2@(h2 ∷ t2)} {_} {a} {f1@(∷-Free _ _ _ _ ft1)} {f2@(∷-Free _ _ min2 incomp2 _)} {f3} PE.refl a∈l3 | l⊑r h1⊑h2 ¬h2⊑h1 = 
  let
    p : (a ∈ t1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) t1) ⊎ (a ∈ t1 × a ∈ l2) 
    p = ∨-lemma {f1 = ft1} {f2 = f2} {f3 = f3} PE.refl a∈l3
  in
    ([_,_] c1) ([_,_] c2 c3) p
  where
    c1 : (a ∈ t1 × ¬ Any (a ⊑_) l2) → (a ∈ l1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c1 (a∈t1 , ¬a⊑l2) = inj₁ $ (there a∈t1 , ¬a⊑l2)

    ¬a⊑l1 : a ∈ l2 → ¬ Any (a ⊑_) t1 → ¬ Any (a ⊑_) l1
    ¬a⊑l1 a∈l2 ¬a⊑t1 (there a⊑t1) = 
      ¬a⊑t1 a⊑t1
    ¬a⊑l1 (here a≡h2) ¬a⊑t1 (here a⊑h1) = 
      ¬h2⊑h1 (transitive⊑ (reflexive $ PE.sym a≡h2) a⊑h1)
    ¬a⊑l1 (there a∈t2) ¬a⊑t1 (here a⊑h1) =
      incomp2 $ LAny.map (λ x≡a → inj₂ $ transitive⊑ (transitive⊑ (reflexive (PE.sym x≡a)) a⊑h1) h1⊑h2) a∈t2
    
    c2 : (a ∈ l2 × ¬ Any (a ⊑_) t1) → (a ∈ l1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈ l1 × a ∈ l2) 
    c2 (a∈l2 , ¬a⊑t1) = inj₂ $ inj₁ $ (a∈l2 , ¬a⊑l1 a∈l2 ¬a⊑t1)

    c3 : (a ∈ t1 × a ∈ l2) → (a ∈ l1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c3 (a∈t1 , a∈l2) = inj₂ $ inj₂ (there a∈t1 , a∈l2)
∨-lemma {l1@(h1 ∷ t1)} {l2@(h2 ∷ t2)} {_} {a} {f1@(∷-Free _ _ _ incomp1 _)} {f2@(∷-Free _ _ _ _ ft2)} {f3} PE.refl a∈l3 | r⊑l ¬h1⊑h2 h2⊑h1 = 
  let 
    p : (a ∈ l1 × ¬ Any (a ⊑_) t2) ⊎ (a ∈ t2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈ l1 × a ∈ t2)
    p = (∨-lemma {f1 = f1} {f2 = ft2} {f3 = f3} PE.refl a∈l3)
  in
    ([_,_] c1) ([_,_] c2 c3) p
  where
    ¬a⊑l2 : a ∈ l1 → ¬ Any (a ⊑_) t2 → ¬ Any (a ⊑_) l2
    ¬a⊑l2 a∈l1 ¬a⊑t2 (there a⊑t2) = 
      ¬a⊑t2 a⊑t2
    ¬a⊑l2 (here a≡h1) ¬a⊑t2 (here a⊑h2) = 
      ¬h1⊑h2 $ transitive⊑ (reflexive $ PE.sym a≡h1) a⊑h2
    ¬a⊑l2 (there a∈t1) ¬a⊑t2 (here a⊑h2) =
      incomp1 $ LAny.map (λ x≡a → inj₂ $ transitive⊑ (transitive⊑ (reflexive (PE.sym x≡a)) a⊑h2) h2⊑h1) a∈t1
      
    c1 : (a ∈ l1 × ¬ Any (a ⊑_) t2) → (a ∈ l1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c1 (a∈l1 , ¬a⊑t2) = inj₁ $ (a∈l1 , ¬a⊑l2 a∈l1 ¬a⊑t2 )

    c2 : (a ∈ t2 × ¬ Any (a ⊑_) l1) → (a ∈ l1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c2 (a∈t2 , ¬a⊑l1) = inj₂ $ inj₁ $ (there a∈t2 , ¬a⊑l1)

    c3 : (a ∈ l1 × a ∈ t2) → (a ∈ l1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c3 (a∈l1 , a∈t2) = inj₂ $ inj₂ (a∈l1 , there a∈t2)
∨-lemma {l1@(h1 ∷ t1)} {l2@(.h1 ∷ t2)} {_} {a} {f1@(∷-Free _ _ _ _ ft1)} {f2@(∷-Free _ _ _ incomp2 _)} {f3} PE.refl a∈l3 | l≡r h1≡h2@PE.refl = 
  let
    p : (a ∈ t1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) t1) ⊎ (a ∈ t1 × a ∈ l2) 
    p = (∨-lemma {f1 = ft1} {f2 = f2} {f3 = f3} PE.refl a∈l3)
  in
  [_,_] c1 ([_,_] c2 c3) p
  where
    c1 : (a ∈ t1 × ¬ Any (a ⊑_) l2) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c1 (a∈t1 , ¬a⊑l1) = inj₁ $ (there a∈t1 , ¬a⊑l1)

    c2 : (a ∈ l2 × ¬ Any (a ⊑_) t1) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c2 ((here a≡h1) , ¬a⊑t1) = 
      inj₂ $ inj₂ $ (here a≡h1 , here a≡h1)
    c2 ((there a∈t2) , ¬a⊑t1) with a ∦? h1
    c2 ((there a∈t2) , ¬a⊑t1) | l⊑r a⊑h1 ¬h1⊑a = 
      ⊥-elim $ incomp2 $ (LAny.map (λ a≡x → inj₂ $ transitive⊑ (reflexive $ PE.sym a≡x) a⊑h1) a∈t2)
    c2 ((there a∈t2) , ¬a⊑t1) | r⊑l ¬a⊑h1 h1⊑a =
      ⊥-elim $ incomp2 $ (LAny.map (λ a≡x → inj₁ $ transitive⊑ h1⊑a (reflexive a≡x)) a∈t2)
    c2 ((there a∈t2) , ¬a⊑t1) | l≡r a≡h1 =
      inj₂ $ inj₂ $ (here a≡h1 , here a≡h1)
    c2 ((there a∈t2) , ¬a⊑t1) | l∥r a∥h1 =
      inj₂ $ inj₁ $ (there a∈t2 , ¬a⊑l1)
      where
        ¬a⊑l1 : ¬ (Any (a ⊑_) l1)
        ¬a⊑l1 (here a⊑h1) = a∥h1 (inj₁ a⊑h1)
        ¬a⊑l1 (there a⊑t1) = ¬a⊑t1 a⊑t1

    c3 : (a ∈ t1 × a ∈ l2) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c3 (a∈t1 , a∈l2) = inj₂ $ inj₂ $ (there a∈t1 , a∈l2) 

∨-lemma {h1 ∷ t1} {h2 ∷ t2} {_} {a} {f1} {f2} {f3} PE.refl a∈l3 | l∥r h1∥h2 with compare h1 h2
∨-lemma {.a ∷ t1} {h2 ∷ t2} {_} {a} {f1} {f2@(∷-Free _ _ min2 _ _)} {f3} PE.refl (here a≡h1@PE.refl) | l∥r a∥h2 | tri< a<h2 _ _ =
  inj₁ $ ((here PE.refl) , ¬a⊑l2)
  where
    ¬a⊑l2 : ¬  Any (a ⊑_) (h2 ∷ t2)
    ¬a⊑l2 (here a⊑h2) = a∥h2 (inj₁ a⊑h2) 
    ¬a⊑l2 (there a⊑t2) = anyEliminate t2 eliminator a⊑t2
      where
        eliminator : AnyEliminator Carrier ⊥ (a ⊑_) t2
        eliminator x f a⊑x x∈t2 = (unimodality a<h2 (LA.lookup min2 x∈t2) (inj₁ $ reflexive {a} {a} PE.refl) a∥h2) (inj₁ a⊑x)
∨-lemma {l1@(h1 ∷ t1)} {l2@(h2 ∷ t2)} {_} {a} {f1@(∷-Free _ _ _ _ ft1)} {f2@(∷-Free _ _ min2 _ _)} {f3} PE.refl (there a∈t1∨l2) | l∥r h1∥h2 | tri< a<h2 _ _ =
  let 
    p = ∨-lemma {a = a} {f1 = ft1} {f2 = f2} {f3 = ∨-free ft1 f2} PE.refl a∈t1∨l2
  in
    {!!}
  where
    c1 : (a ∈ t1 × ¬ Any (a ⊑_) l2) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c1 (a∈t1 , ¬a⊑l2) = inj₁ $ (there a∈t1 , ¬a⊑l2)

    c2 : (a ∈ l2 × ¬ Any (a ⊑_) t2) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c2 (a∈l2 , ¬a⊑t1) = {!!}

    c3 : (a ∈ t1 × a ∈ l2) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c3 (a∈t1 , a∈t2) = {!!}

∨-lemma {h1 ∷ t1} {h2 ∷ t2} {_} {a} {f1} {f2@(∷-Free _ _ min2 _ _)} {f3} PE.refl a∈l3 | l∥r h1∥h2 | tri≈ _ a≡h2 _ =
  {!a!}
  
