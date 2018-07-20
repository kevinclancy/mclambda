open import Function using (_$_)
open import Data.Empty
open import Data.List
open import Data.List.All as LA
open import Data.List.Any
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

module FreeSemilattice.Semilattice (P : DeltaPoset0) where


open import FreeSemilattice P renaming (_≤_ to _≤'_)
open import FreeSemilattice.Poset P as PS renaming (_≈_ to _≈'_)

open DeltaPoset0 P


infix 4 _≈_ _≤_
infixr 6 _∨'_
infixr 6 _∨_

private
 -- redeclared to control fixity relative to join operators
 _≤_ = _≤'_
 _≈_ = _≈'_

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

∨-idem : (l : List Carrier) → l ∨ [] ≡ l
∨-idem [] = PE.refl
∨-idem (x ∷ l) = PE.refl

∨-idemˡ : (l : List Carrier) → [] ∨ l ≡ l
∨-idemˡ [] = PE.refl
∨-idemˡ (x ∷ l) = PE.refl

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

-- todo: l ∨ k → IsFreeList l → IsFreeList k → IsFreeList l ∨ k
∨-free : (l1 l2 : List Carrier) → IsFreeList _<_ _⊑_ l1 → IsFreeList _<_ _⊑_ l2 → IsFreeList _<_ _⊑_ (l1 ∨ l2)
∨-free [] l2 f1 f2 = f2
∨-free (h1 ∷ t1) [] f1 f2 = f1
∨-free (h1 ∷ t1) (h2 ∷ t2) f1@(∷-Free h1 t1 min1 incomp1 ft1) f2@(∷-Free h2 t2 min2 incomp2 ft2) with h1 ∦? h2
... | l⊑r h1⊑h2 ¬h2⊑h1  = ∨-free t1 (h2 ∷ t2) ft1 f2 
... | r⊑l ¬h1⊑h2 h2⊑h1 = ∨-free (h1 ∷ t1) t2 f1 ft2
... | l≡r h1≡h2 = ∨-free t1 (h2 ∷ t2) ft1 f2
... | l∥r h1∥h2 with h1 <? h2
... | yes h1<h2 = ∷-Free h1 (t1 ∨ (h2 ∷ t2)) min incomp (∨-free t1 (h2 ∷ t2) ft1 f2) 
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
... | no ¬h1<h2 = ∷-Free h2 ((h1 ∷ t1) ∨ t2) min incomp (∨-free (h1 ∷ t1) t2 f1 ft2)  
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
    
⊥' : Carrier-FP
⊥' = ([] , []-Free)

⊥'-min :  Minimum _≤_ ⊥'
⊥'-min x = []-≤

_∨'_ : Carrier-FP → Carrier-FP → Carrier-FP
_∨'_ (l1 , f1) (l2 , f2) = (l1 ∨ l2 , ∨-free l1 l2 f1 f2) 

∨'-idemʳ : (s : Carrier-FP) → (s ∨' ⊥' ≈ s)
∨'-idemʳ (l , f) = ∨-idem l

∨'-idemˡ : (s : Carrier-FP) → (⊥' ∨' s ≈ s) 
∨'-idemˡ (l , f) = ∨-idemˡ l

∨-discardˡ : (h1 h2 : Carrier) → (t1 t2 : List Carrier) → (h1 ⊑ h2) →
                ((h1 ∷ t1) ∨ (h2 ∷ t2) ≡ t1 ∨ (h2 ∷ t2))
∨-discardˡ h1 h2 t1 t2 h1⊑h2 with h1 ∦? h2
∨-discardˡ h1 h2 t1 t2 h1⊑h2 | l⊑r _ ¬h2⊑h1 = PE.refl
∨-discardˡ h1 h2 t1 t2 h1⊑h2 | r⊑l ¬h1⊑h2 _ = ⊥-elim $ ¬h1⊑h2 h1⊑h2
∨-discardˡ h1 h2 t1 t2 h1⊑h2 | l≡r PE.refl = PE.refl
∨-discardˡ h1 h2 t1 t2 h1⊑h2 | l∥r h1∥h2 = ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)

∨-push : ∀ {h : Carrier} → {l1 l2 : List Carrier} → (All (h <_) l1) → ¬ (Any (h ∦_) l1) → (All (h <_) l2) → ¬ (Any (h ∦_) l2) → (h ∷ (l1 ∨ l2) ≡ ((h ∷ l1) ∨ l2))
∨-push {h} {l1} {[]} min1 incomp1 min2 incomp2 rewrite (∨-idem l1) = PE.refl
∨-push {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 with h ∦? h2
∨-push {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | l⊑r h⊑h2 ¬h2⊑h = ⊥-elim $ incomp2 (here $ inj₁ h⊑h2)
∨-push {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | r⊑l ¬h⊑h2 h2⊑h = ⊥-elim $ incomp2 (here $ inj₂ h2⊑h)
∨-push {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | l≡r h≡h2@PE.refl = ⊥-elim $ incomp2 (here $ inj₁ (reflexive PE.refl))
∨-push {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | l∥r h∥h2 with h <? h2
∨-push {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | l∥r h∥h2 | yes h<h2 = PE.refl
∨-push {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | l∥r h∥h2 | no ¬h<h2 = ⊥-elim $ ¬h<h2 (head min2)

∨-comm : (l1 l2 : List Carrier) → IsFreeList _<_ _⊑_ l1 → IsFreeList _<_ _⊑_ l2 → (l1 ∨ l2) ≡ (l2 ∨ l1)
∨-comm [] k f1 f2 = PE.sym (∨-idem k)
∨-comm (h1 ∷ t1) [] f1 f2 = PE.refl
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 with h1 ∦? h2
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l⊑r h1⊑h2 ¬h2⊑h1 with h2 ∦? h1
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l⊑r h1⊑h2 ¬h2⊑h1 | l⊑r h2⊑h1 ¬h1⊑h2 = ⊥-elim $ ¬h1⊑h2 h1⊑h2
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1@(∷-Free _ _ _ _ ft1) f2 | l⊑r h1⊑h2 ¬h2⊑h1 | DeltaPoset0.r⊑l x x₁ = ∨-comm t1 (h2 ∷ t2) ft1 f2
∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1@(∷-Free _ _ min1 incomp1 ft1) f2@(∷-Free _ _ min2 incomp2 ft2) | l⊑r h1⊑h2 ¬h2⊑h1 | DeltaPoset0.l≡r h1≡h2@PE.refl = 
    begin
    t1 ∨ (h1 ∷ t2) ≡⟨ ∨-comm t1 (h1 ∷ t2) ft1 f2 ⟩
    (h1 ∷ t2) ∨ t1 ≡⟨ PE.sym $ ∨-push min2 incomp2 min1 incomp1 ⟩
    h1 ∷ (t2 ∨ t1) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm t2 t1 ft2 ft1 ⟩
    h1 ∷ (t1 ∨ t2) ≡⟨ ∨-push min1 incomp1 min2 incomp2 ⟩
    (h1 ∷ t1) ∨ t2 ≡⟨ ∨-comm (h1 ∷ t1) t2 f1 ft2 ⟩
    t2 ∨ (h1 ∷ t1)
    ∎
    where
    open PE.≡-Reasoning
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h1 = ⊥-elim $ h2∥h1 (inj₂ h1⊑h2) 
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | r⊑l ¬h1⊑h2 h2⊑h1 with h2 ∦? h1
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2@(∷-Free _ _ _ _ ft2) | r⊑l ¬h1⊑h2 h2⊑h1 | l⊑r _ _ = ∨-comm (h1 ∷ t1) t2 f1 ft2
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | r⊑l ¬h1⊑h2 h2⊑h1 | r⊑l ¬h2⊑h1 h1⊑h2 = ⊥-elim $ ¬h1⊑h2 h1⊑h2
∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1 f2 | r⊑l ¬h1⊑h1 h1⊑h1 | l≡r h1≡h2@PE.refl = ⊥-elim $ ¬h1⊑h1 h1⊑h1
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | DeltaPoset0.r⊑l ¬h1⊑h2 h2⊑h1 | l∥r h1∥h2 = ⊥-elim $ h1∥h2 (inj₁ h2⊑h1)
∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l≡r h1≡h2@PE.refl with h1 ∦? h1 
∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l≡r h1≡h2@PE.refl | l⊑r h1⊑h1 ¬h1⊑h1 = ⊥-elim $ ¬h1⊑h1 h1⊑h1
∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l≡r h1≡h2@PE.refl | r⊑l ¬h1⊑h1 h1⊑h1 = ⊥-elim $ ¬h1⊑h1 h1⊑h1
∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l≡r h1≡h2@PE.refl | l≡r _ = 
    begin
    t1 ∨ (h1 ∷ t2) ≡⟨ ∨-comm t1 (h1 ∷ t2) ft1 f2 ⟩
    (h1 ∷ t2) ∨ t1 ≡⟨ PE.sym $ ∨-push min2 incomp2 min1 incomp1 ⟩
    h1 ∷ (t2 ∨ t1) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm t2 t1 ft2 ft1 ⟩
    h1 ∷ (t1 ∨ t2) ≡⟨ ∨-push min1 incomp1 min2 incomp2 ⟩
    (h1 ∷ t1) ∨ t2 ≡⟨ ∨-comm (h1 ∷ t1) t2 f1 ft2 ⟩
    t2 ∨ (h1 ∷ t1)
    ∎
    where
    open PE.≡-Reasoning
∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l≡r h1≡h2@PE.refl | l∥r h1∥h1 = ⊥-elim $ h1∥h1 (∦-refl h1)
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 with h1 <? h2 
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 | yes h1<h2 with h2 ∦? h1
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 | yes h1<h2 | l⊑r h2⊑h1 ¬h1⊑h2 = ⊥-elim $ h1∥h2 (inj₂ h2⊑h1)
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 | yes h1<h2 | r⊑l ¬h2⊑h1 h1⊑h2 = ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)
∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1 f2 | l∥r h1∥h1 | yes h1<h1 | l≡r h1≡h2@PE.refl = ⊥-elim $ h1∥h1 (∦-refl h1)
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 | yes h1<h2 | l∥r h2∥h1 with h2 <? h1 
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 | yes h1<h2 | l∥r h2∥h1 | yes h2<h1 with h1≡h2 
    where 
    h1≡h2 : h1 ≡ h2
    h1≡h2 with compare h1 h2
    h1≡h2 | tri< _ _ ¬h2<h1 = ⊥-elim $ ¬h2<h1 h2<h1
    h1≡h2 | tri≈ _ h1≡h2 _ = h1≡h2
    h1≡h2 | tri> ¬h1<h2 _ _ = ⊥-elim $ ¬h1<h2 h1<h2
∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l∥r h1∥h1 | yes h1<h1 | l∥r _ | yes _ | PE.refl = 
    begin
    h1 ∷ (t1 ∨ (h1 ∷ t2)) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm t1 (h1 ∷ t2) ft1 f2 ⟩
    h1 ∷ ((h1 ∷ t2) ∨ t1) ≡⟨ PE.cong (λ x → h1 ∷ x) $ PE.sym (∨-push min2 incomp2 min1 incomp1) ⟩
    h1 ∷ h1 ∷ (t2 ∨ t1) ≡⟨ PE.cong (λ x → h1 ∷ h1 ∷ x) $ ∨-comm t2 t1 ft2 ft1 ⟩
    h1 ∷ h1 ∷ (t1 ∨ t2) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-push min1 incomp1 min2 incomp2 ⟩
    h1 ∷ ((h1 ∷ t1) ∨ t2) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm (h1 ∷ t1) t2 f1 ft2 ⟩ 
    h1 ∷ (t2 ∨ (h1 ∷ t1))
    ∎
    where
    open PE.≡-Reasoning
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) | l∥r h1∥h2 | yes h1<h2 | l∥r h2∥h1 | no ¬h2<h1 = 
    PE.cong (λ x → h1 ∷ x) $ ∨-comm t1 (h2 ∷ t2) ft1 f2
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 | no ¬h1<h2 with h2 ∦? h1 
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 | no ¬h1<h2 | l⊑r h2⊑h1 ¬h1⊑h2 = ⊥-elim $ h1∥h2 (inj₂ h2⊑h1)
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 | no ¬h1<h2 | r⊑l ¬h2⊑h1 h1⊑h2 = ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)
∨-comm (.h2 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h2∥h2 | no ¬h2<h2 | l≡r h2≡h1@PE.refl = ⊥-elim $ h2∥h2 (∦-refl h2) 
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 | no ¬h1<h2 | l∥r _ with h2 <? h1
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2@(∷-Free .h2 .t2 min2 incomp2 ft2) | l∥r h1∥h2 | no ¬h1<h2 | l∥r _ | yes h2<h1 = 
    PE.cong (λ x → h2 ∷ x) $ ∨-comm (h1 ∷ t1) t2 f1 ft2 
∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l∥r h1∥h2 | no ¬h1<h2 | l∥r _ | no ¬h2<h1 with h1≡h2 
    where
    h1≡h2 : h1 ≡ h2
    h1≡h2 with compare h1 h2
    h1≡h2 | tri< h1<h2 _ _ = ⊥-elim $ ¬h1<h2 h1<h2
    h1≡h2 | tri≈ _ goal _ = goal
    h1≡h2 | tri> _ _ h2<h1 = ⊥-elim $ ¬h2<h1 h2<h1
∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l∥r h1∥h1 | no ¬h1<h1 | l∥r _ | no _ | PE.refl =
    begin
    h1 ∷ ((h1 ∷ t1) ∨ t2) ≡⟨ PE.cong (λ x → h1 ∷ x) $ PE.sym (∨-push min1 incomp1 min2 incomp2) ⟩
    h1 ∷ h1 ∷ (t1 ∨ t2) ≡⟨ PE.cong (λ x → h1 ∷ h1 ∷ x) $ ∨-comm t1 t2 ft1 ft2 ⟩
    h1 ∷ h1 ∷ (t2 ∨ t1) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-push min2 incomp2 min1 incomp1 ⟩
    h1 ∷ ((h1 ∷ t2) ∨ t1)
    ∎
    where
    open PE.≡-Reasoning

∨'-comm : (s1 s2 : Carrier-FP) → (s1 ∨' s2 ≈ s2 ∨' s1)
∨'-comm (l1 , f1) (l2 , f2) = ∨-comm l1 l2 f1 f2

∨-discardʳ : {h1 h2 : Carrier} → {t1 t2 : List Carrier} → IsFreeList _<_ _⊑_ (h1 ∷ t1) → IsFreeList _<_ _⊑_ (h2 ∷ t2) → (h2 ⊑ h1) →
                ((h1 ∷ t1) ∨ (h2 ∷ t2) ≡ (h1 ∷ t1) ∨ t2)
∨-discardʳ {h1} {h2} {t1} {t2} f1 f2@(∷-Free _ _ _ _ ft2) h2⊑h1 =
    begin
    (h1 ∷ t1) ∨ (h2 ∷ t2) ≡⟨ ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 ⟩
    (h2 ∷ t2) ∨ (h1 ∷ t1) ≡⟨ ∨-discardˡ h2 h1 t2 t1 h2⊑h1  ⟩
    t2 ∨ (h1 ∷ t1) ≡⟨ ∨-comm t2 (h1 ∷ t1) ft2 f1 ⟩
    (h1 ∷ t1) ∨ t2
    ∎
    where
    open PE.≡-Reasoning

∨-any-⊑ : {x : Carrier} → {l1 l2 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → (Any (x ⊑_) l1) → (Any (x ⊑_) (l1 ∨ l2))
∨-any-⊑ {x} {[]} {l2} f1 f2 p = ⊥-elim $ LAP.¬Any[] p
∨-any-⊑ {x} {h1 ∷ t1} {[]} f1 f2 (here px) = here px
∨-any-⊑ {x} {h1 ∷ t1} {[]} f1 f2 (there p) = there p 
∨-any-⊑ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2 p with h1 ∦? h2
∨-any-⊑ {x} {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (here px) | l⊑r h1⊑h2 ¬h2⊑h1 rewrite (∨-comm t1 (h2 ∷ t2) ft1 f2) = 
    ∨-any-⊑ f2 ft1 (here (transitive⊑ px h1⊑h2))
∨-any-⊑ {x} {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (there p) | l⊑r h1⊑h2 ¬h2⊑h1 = 
    ∨-any-⊑ ft1 f2 p
∨-any-⊑ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) p | r⊑l ¬h1⊑h2 h2⊑h1 = 
    ∨-any-⊑ f1 ft2 p
∨-any-⊑ {x} {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (here px) | l≡r PE.refl rewrite (∨-comm t1 (h1 ∷ t2) ft1 f2) = 
    ∨-any-⊑ f2 ft1 (here px)
∨-any-⊑ {x} {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (there p) | l≡r PE.refl = 
    ∨-any-⊑ ft1 f2 p
∨-any-⊑ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2 p | l∥r h1∥h2 with compare h1 h2 
∨-any-⊑ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2 (here px) | l∥r h1∥h2 | tri< h1<h2 _ _ = 
    here px
∨-any-⊑ {x} {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (there p) | l∥r h1∥h2 | tri< h1<h2 _ _ = 
    there (∨-any-⊑ ft1 f2 p)
∨-any-⊑ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2 p | l∥r h1∥h2 | tri≈ _ h1≡h2@PE.refl _ = 
    ⊥-elim $ h1∥h2 (∦-refl h1)
∨-any-⊑ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) p | l∥r h1∥h2 | tri> _ _ h2<h1 = 
    there (∨-any-⊑ f1 ft2 p)

incomp-lemma : {h1 h2 : Carrier} → {t2 : List Carrier} → (h1<h2 : h1 < h2) → (min2 : All (h2 <_) t2) → (h1∥h2 : h1 ∥ h2) → ¬ (Any (h1 ∦_) (h2 ∷ t2))
incomp-lemma {h1} {h2} {t2} h1<h2 min2 h1∥h2 (here h1∦h2) = h1∥h2 h1∦h2
incomp-lemma {h1} {h2} {t2} h1<h2 min2 h1∥h2 (there h1∦t2) = anyEliminate t2 eliminator h1∦t2 
    where
    eliminator : AnyEliminator Carrier ⊥ (h1 ∦_) t2
    eliminator a f h1∦a a∈t2 = (unimodality h1<h2 (LA.lookup min2 a∈t2) (∦-refl h1) h1∥h2) h1∦a

any-⊑-push : {h1 : Carrier} → {t1 l2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ (h1 ∷ t1)} → {ft1 : IsFreeList _<_ _⊑_ t1} → 
                {f2 : IsFreeList _<_ _⊑_ l2} → ((t1 , ft1) ≤ (l2 , f2)) → (Any (h1 ⊑_) l2) → (((h1 ∷ t1) , f1) ≤ (l2 , f2))  
any-⊑-push {h1} {.[]} {h2 ∷ t2} {f1} {.[]-Free} {f2} []-≤ (here h1⊑h2) = 
    cmp-≤ []-Free f1 f2 h1⊑h2 []-≤
any-⊑-push {h1} {.[]} {h2 ∷ t2} {f1} {.[]-Free} {f2@(∷-Free _ _ _ _ ft2)} []-≤ (there any-h1⊑t2) = 
    ≤-push h1≤t2 
    where
    h1≤t2 : (h1 ∷ [] , f1) ≤ (t2 , ft2)
    h1≤t2 = any-⊑-push []-≤ any-h1⊑t2
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1} {ft1} {f2} t1≤l2@(cmp-≤ ft1t _ _ t1h⊑h2 t1t≤h2) (here h1⊑h2) = 
    cmp-≤ ft1 f1 f2 h1⊑h2 t1≤l2
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1} {ft1} {f2@(∷-Free _ _ _ _ ft2)} t1≤l2@(cmp-≤ ft1t _ _ t1h⊑h2 t1t≤h2) (there any-h1⊑t2) with h1 ∦? h2
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1} {ft1} {f2@(∷-Free .h2 .t2 _ _ ft2)} t1≤l2@(cmp-≤ ft1t _ .(∷-Free h2 t2 _ _ ft2) t1h⊑h2 t1t≤h2) (there any-h1⊑t2) | l⊑r h1⊑h2 ¬h2⊑h1 = 
    cmp-≤ ft1 f1 f2 h1⊑h2 t1≤l2
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1@(∷-Free _ _ _ incomp1 _)} {_} {∷-Free .h2 .t2 _ _ ft2} (cmp-≤ ft1t _ .(∷-Free h2 t2 _ _ ft2) t1h⊑h2 t1t≤h2) (there any-h1⊑t2) | r⊑l ¬h1⊑h2 h2⊑h1 = 
    ⊥-elim $ incomp1 $ here (inj₂ (transitive⊑ t1h⊑h2 h2⊑h1))
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1} {ft1} {f2@(∷-Free .h2 .t2 _ _ ft2)} t1≤l2@(cmp-≤ ft1t _ .(∷-Free h2 t2 _ _ ft2) t1h⊑h2 t1t≤h2) (there any-h1⊑t2) | l≡r h1≡h2 = 
    cmp-≤ ft1 f1 f2 (reflexive h1≡h2) t1≤l2
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1} {ft1} {f2} (cmp-≤ ft1t _ (∷-Free _ _ _ _ ft2) t1h⊑h2 t1t≤h2) (there any-h1⊑t2) | l∥r h1∥h2 with compare h1 h2
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1} {ft1} {f2@(∷-Free .h2 .t2 min2 _ _)} t1≤l2@(cmp-≤ ft1t _ (∷-Free .h2 .t2 _ _ ft2) t1h⊑h2 t1t≤h2) (there any-h1⊑t2) | l∥r h1∥h2 | tri< h1<h2 _ _ =
    ⊥-elim $ (incomp-lemma h1<h2 min2 h1∥h2) (there $ Data.List.Any.map (λ h1⊑x → inj₁ h1⊑x) any-h1⊑t2)
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1} {ft1} {f2@(∷-Free .h2 .t2 _ _ _)} t1≤l2@(cmp-≤ ft1t _ (∷-Free .h2 .t2 _ _ ft2) t1h⊑h2 t1t≤h2) (there any-h1⊑t2) | l∥r h1∥h2 | tri≈ _ h1≡h2 _ =
    cmp-≤ ft1 f1 f2 (reflexive h1≡h2) t1≤l2
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1@(∷-Free _ _ min1 _ _)} {ft1} {f2@(∷-Free .h2 .t2 _ _ _)} t1≤l2@(cmp-≤ ft1t _ (∷-Free .h2 .t2 _ _ ft2) t1h⊑h2 t1t≤h2) (there any-h1⊑t2) | l∥r h1∥h2 | tri> _ _ h2<h1 =
    ⊥-elim $ (unimodality h2<h1 (head min1) (∦-refl h2) (∥-sym h1∥h2)) (inj₂ t1h⊑h2)
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1} {ft1} {f2} t1≤l2@(skip-≤ ft1 ft2 f2 h2<t1h t1h∥h2 t1≤t2) (here px) = 
    cmp-≤ ft1 f1 f2 px t1≤l2
any-⊑-push {h1} {t1h ∷ t1t} {h2 ∷ t2} {f1} {ft1} {f2} (skip-≤ ft1 ft2 f2 h2<t1h t1h∥h2 t1≤t2) (there any-h1⊑t2) = 
    (≤-push (any-⊑-push t1≤t2 any-h1⊑t2)) 

-- *** Note that inflativeness is just a special case of monotonicity (combined with ⊥'-minimum)!!! should be useful for proving lub 
∨'-monoʳ : (s1 : Carrier-FP) → {s2 s3 : Carrier-FP} → (s2 ≤ s3) → (s1 ∨' s2 ≤ s1 ∨' s3)
∨'-monoʳ ([] , f1) {.[] , .[]-Free} {[] , f3} []-≤ = []-≤
∨'-monoʳ (h1 ∷ t1 , f1) {.[] , .[]-Free} {[] , f3} []-≤ = ≤-refl PE.refl
∨'-monoʳ ([] , f1) {.[] , .[]-Free} {h3 ∷ t3 , f3} []-≤ = []-≤
∨'-monoʳ (h1 ∷ t1 , f1@(∷-Free _ _ min1 incomp1 ft1)) {.[] , .[]-Free} {h3 ∷ t3 , f3@(∷-Free _ _ min3 incomp3 ft3)} []-≤ with h1 ∦? h3
∨'-monoʳ (h1 ∷ t1 , f1@(∷-Free _ _ min1 incomp1 ft1)) {.[] , .[]-Free} {s3@(h3 ∷ t3 , f3@(∷-Free _ _ min3 incomp3 ft3))} []-≤ | l⊑r h1⊑h3 ¬h3⊑h1 = 
    let 
      t1≤t1∨l3 : (t1 , ft1) ≤ ((t1 , ft1) ∨' ((h3 ∷ t3), f3))
      t1≤t1∨l3 = 
        begin
          (t1 , ft1) ≈⟨ ≈-sym {(t1 , ft1) ∨' ⊥'} {t1 , ft1} $ ∨'-idemʳ (t1 , ft1) ⟩
          (t1 , ft1) ∨' ⊥' ≤⟨ ∨'-monoʳ (t1 , ft1) (⊥'-min s3) ⟩
          (t1 , ft1) ∨' (h3 ∷ t3 , f3)
         ∎
    in any-⊑-push t1≤t1∨l3 h1⊑t1∨l3
    
    where
      open import Relation.Binary.PartialOrderReasoning FP-Poset0

      h1⊑t1∨l3 : Any (h1 ⊑_) (t1 ∨ (h3 ∷ t3))
      h1⊑t1∨l3 rewrite (∨-comm t1 (h3 ∷ t3) ft1 f3) = ∨-any-⊑ f3 ft1 (here h1⊑h3)
∨'-monoʳ (h1 ∷ t1 , f1@(∷-Free _ _ min1 incomp1 ft1)) {.[] , .[]-Free} {s3@(h3 ∷ t3 , f3@(∷-Free _ _ min3 incomp3 ft3))} []-≤ | r⊑l ¬h1⊑h3 h3⊑h1 = 
  ∨'-monoʳ (h1 ∷ t1 , f1) (⊥'-min $ t3 , ft3)
∨'-monoʳ (h1 ∷ t1 , f1@(∷-Free _ _ min1 incomp1 ft1)) {.[] , .[]-Free} {s3@(h3 ∷ t3 , f3@(∷-Free _ _ min3 incomp3 ft3))} []-≤ | l≡r h1≡h3 = 
    let 
      t1≤t1∨l3 : (t1 , ft1) ≤ ((t1 , ft1) ∨' ((h3 ∷ t3), f3))
      t1≤t1∨l3 = 
        begin
          (t1 , ft1) ≈⟨ ≈-sym {(t1 , ft1) ∨' ⊥'} {t1 , ft1} $ ∨'-idemʳ (t1 , ft1) ⟩
          (t1 , ft1) ∨' ⊥' ≤⟨ ∨'-monoʳ (t1 , ft1) (⊥'-min s3) ⟩
          (t1 , ft1) ∨' (h3 ∷ t3 , f3)
         ∎
    in any-⊑-push t1≤t1∨l3 h1⊑t1∨l3
    
    where
      open import Relation.Binary.PartialOrderReasoning FP-Poset0

      h1⊑t1∨l3 : Any (h1 ⊑_) (t1 ∨ (h3 ∷ t3))
      h1⊑t1∨l3 rewrite (∨-comm t1 (h3 ∷ t3) ft1 f3) = ∨-any-⊑ f3 ft1 (here (reflexive h1≡h3))
∨'-monoʳ (h1 ∷ t1 , f1@(∷-Free _ _ min1 incomp1 ft1)) {.[] , .[]-Free} {s3@(h3 ∷ t3 , f3@(∷-Free _ _ min3 incomp3 ft3))} []-≤ | l∥r h1∥h3 with compare h1 h3
∨'-monoʳ (h1 ∷ t1 , f1@(∷-Free _ _ min1 incomp1 ft1)) {.[] , .[]-Free} {s3@(h3 ∷ t3 , f3@(∷-Free _ _ min3 incomp3 ft3))} []-≤ | l∥r h1∥h3 | tri< h1<h3 _ _ =
    let 
      t1≤t1∨l3 : (t1 , ft1) ≤ ((t1 , ft1) ∨' ((h3 ∷ t3), f3))
      t1≤t1∨l3 = 
        begin
          (t1 , ft1) ≈⟨ ≈-sym {(t1 , ft1) ∨' ⊥'} {t1 , ft1} $ ∨'-idemʳ (t1 , ft1) ⟩
          (t1 , ft1) ∨' ⊥' ≤⟨ ∨'-monoʳ (t1 , ft1) (⊥'-min s3) ⟩
          (t1 , ft1) ∨' (h3 ∷ t3 , f3)
         ∎
    in any-⊑-push (≤-push {h1} t1≤t1∨l3) (here $ reflexive PE.refl)
  where
    open import Relation.Binary.PartialOrderReasoning FP-Poset0
∨'-monoʳ (h1 ∷ t1 , f1@(∷-Free _ _ min1 incomp1 ft1)) {.[] , .[]-Free} {s3@(h3 ∷ t3 , f3@(∷-Free _ _ min3 incomp3 ft3))} []-≤ | l∥r h1∥h3 | tri≈ _ h1≡h3 _ =
    let 
      l1≤l1∨t3 : (h1 ∷ t1 , f1) ≤ ((h1 ∷ t1 , f1) ∨' (t3 , ft3))
      l1≤l1∨t3 = 
        begin
          (h1 ∷ t1 , f1) ≈⟨ ≈-sym {(h1 ∷ t1 , f1) ∨' ⊥'} {h1 ∷ t1 , f1} $ ∨'-idemʳ (h1 ∷ t1 , f1) ⟩
          (h1 ∷ t1 , f1) ∨' ⊥' ≤⟨ ∨'-monoʳ (h1 ∷ t1 , f1) (⊥'-min (t3 , ft3)) ⟩
          (h1 ∷ t1 , f1) ∨' (t3 , ft3)
         ∎
    in ≤-push {h3} l1≤l1∨t3
  where
    open import Relation.Binary.PartialOrderReasoning FP-Poset0

∨'-monoʳ (h1 ∷ t1 , f1@(∷-Free _ _ min1 incomp1 ft1)) {.[] , .[]-Free} {s3@(h3 ∷ t3 , f3@(∷-Free _ _ min3 incomp3 ft3))} []-≤ | l∥r h1∥h3 | tri> _ _ h3<h1 =
  {!!}

∨'-monoʳ (l1 , f1) {.(_ ∷ _) , f2} {.(_ ∷ _) , f3} (cmp-≤ c'-free .f2 .f3 x s2≤s3) = {!!}
∨'-monoʳ (l1 , f1) {.(_ ∷ _) , f2} {.(_ ∷ _) , f3} (skip-≤ .f2 d'-free .f3 x x₁ s2≤s3) = {!!}

∨'-sup : Supremum _≤_ _∨'_ 
∨'-sup ([] , []-Free) ([] , []-Free) = ([]-≤ , []-≤ , least)  
  where 
    least : ∀ z → (⊥' ≤ z) → (⊥' ≤ z) → ((⊥' ∨' ⊥') ≤ z)
    least z p q = []-≤ 
∨'-sup ([] , []-Free) s@(h2 ∷ t2 , f2) rewrite ∨'-idemˡ s =  ([]-≤ , ≤-refl PE.refl , least) 
  where 
    least : ∀ z → (p : ⊥' ≤ z) → (q : s ≤ z) → (s ≤ z)
    least z p q = q 
∨'-sup s@(h1 ∷ t1 , f1) ([] , []-Free) rewrite ∨'-idemʳ s = (≤-refl PE.refl , []-≤ , least)
  where 
    least : ∀ z → (p : s ≤ z) → (q : ⊥' ≤ z) → (s ≤ z)
    least z p q = p      
∨'-sup s1@(h1 ∷ t1 , f1@(∷-Free .h1 .t1 min1 incomp1 ft1) ) s2@(h2 ∷ t2 , f2@(∷-Free .h2 .t2 min2 incomp2 ft2)) with h1 ∦? h2
∨'-sup (h1 ∷ t1 , f1@(∷-Free .h1 .t1 min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-Free .h2 .t2 min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 = {!!}
  where
    open import Relation.Binary.PartialOrderReasoning FP-Poset0

    goal1 : (h1 ∷ t1 , f1) ≤ (h1 ∷ t1 , f1) ∨' (h2 ∷ t2 , f2)
    goal1 with h1 ∦? h2
    goal1 | l⊑r h1⊑h2 ¬h2⊑h1 = {!!}
      where
        t1≤t1∨l2 : (t1 , ft1) ≤ (t1 , ft1) ∨' (h2 ∷ t2 , f2)
        t1≤t1∨l2 with ∨'-sup (t1 , ft1) (h2 ∷ t2 , f2)
        t1≤t1∨l2 | (a , b , c) = a
        
        l1≤t1∨l2 : (h1 ∷ t1 , f1) ≤ (t1 , ft1) ∨' (h2 ∷ t2 , f2)
        l1≤t1∨l2 = {!!}
    goal1 | DeltaPoset0.r⊑l x x₁ = {!!}
    goal1 | DeltaPoset0.l≡r x = {!!}
    goal1 | DeltaPoset0.l∥r x = {!!} 

∨'-sup (h1 ∷ t1 , ∷-Free .h1 .t1 min1 incomp1 ft1) (h2 ∷ t2 , ∷-Free .h2 .t2 min2 incomp2 ft2) | r⊑l x x₁ = {!!}
∨'-sup (h1 ∷ t1 , ∷-Free .h1 .t1 min1 incomp1 ft1) (h2 ∷ t2 , ∷-Free .h2 .t2 min2 incomp2 ft2) | DeltaPoset0.l≡r x = {!!}
∨'-sup (h1 ∷ t1 , ∷-Free .h1 .t1 min1 incomp1 ft1) (h2 ∷ t2 , ∷-Free .h2 .t2 min2 incomp2 ft2) | DeltaPoset0.l∥r x = {!!}
