module FreeSemilattice where

open import Function using (_$_)
open import Data.Empty
open import Data.List
open import Data.List.All as LA
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE
open import RelationalStructures
open import Util

data IsFreeList {A : Set l0} (_<_ : Rel A l0) (_⊑_ : Rel A l0) : List A → Set l1 where
  []-Free : IsFreeList _<_ _⊑_ []
  ∷-Free : (hd : A) → (tl : List A) → (All (hd <_) tl) → ¬ (Any (λ x → (hd ⊑ x) ⊎ (x ⊑ hd)) tl) → 
            (IsFreeList _<_ _⊑_ tl) → IsFreeList _<_ _⊑_ (hd ∷ tl) 

F⟨_⟩ : DeltaPoset0 → Semilat0
F⟨ P ⟩ = {!!} 
  where 
    open DeltaPoset0 P renaming (trans to tran)

    Carrier-FP : Set₁
    Carrier-FP = Σ[ x ∈ List Carrier ] (IsFreeList _<_ _⊑_ x)

    ≈-FP : Rel Carrier-FP l1  
    ≈-FP = _≡_

    data _≤-FP_ : Carrier-FP → Carrier-FP → Set where
      []-≤ : {cfp : Carrier-FP} → ([] , []-Free) ≤-FP cfp  
      cmp-≤ : {c d : Carrier} {c' d' : List Carrier} → (c'-free : IsFreeList _<_ _⊑_ c') →
              (d'-free : IsFreeList _<_ _⊑_ d') → 
              (c-min : All (c <_) c') → (d-min : All (d <_) d') →
              (c-incomp : ¬ Any (λ x → (c ⊑ x) ⊎ (x ⊑ c)) c') →
              (d-incomp : ¬ Any (λ x → (d ⊑ x) ⊎ (x ⊑ d)) d') →
              ¬ (c < d) → ¬ (d < c) → c ⊑ d →
              (c' , c'-free) ≤-FP (d' , d'-free) →
              (c ∷ c' , ∷-Free c c' c-min c-incomp c'-free) ≤-FP (d ∷ d' , ∷-Free d d' d-min d-incomp d'-free)
      skip-≤ : {c d : Carrier} {c' d' : List Carrier} → (c'-free : IsFreeList _<_ _⊑_ c') → 
               (d'-free : IsFreeList _<_ _⊑_ d') → 
               (c-min : All (c <_) c') → (d-min : All (d <_) d') →
               (c-incomp : ¬ Any (λ x → (c ⊑ x) ⊎ (x ⊑ c)) c') →
               (d-incomp : ¬ Any (λ x → (d ⊑ x) ⊎ (x ⊑ d)) d') →
               (d < c) → (c ∷ c' , ∷-Free c c' c-min c-incomp c'-free) ≤-FP (d' , d'-free) →
               (c ∷ c' , ∷-Free c c' c-min c-incomp c'-free) ≤-FP (d ∷ d' , ∷-Free d d' d-min d-incomp d'-free)

    ∨ : List Carrier → List Carrier → List Carrier
    ∨ [] t2 = t2
    ∨ (h1 ∷ t1) [] = h1 ∷ t1
    ∨ (h1 ∷ t1) (h2 ∷ t2) with h1 ∦? h2
    ∨ (h1 ∷ t1) (h2 ∷ t2) | l⊑r h1⊑h2 ¬h2⊑h1 = ∨ t1 (h2 ∷ t2)
    ∨ (h1 ∷ t1) (h2 ∷ t2) | r⊑l ¬h1⊑h2 h2⊑h1 = ∨ (h1 ∷ t1) t2
    ∨ (h1 ∷ t1) (h2 ∷ t2) | l≡r h1≡h2 = ∨ t1 (h2 ∷ t2)
    ∨ (h1 ∷ t1) (h2 ∷ t2) | l∥r h1∥h2 with h1 <? h2
    ... | yes h1<h2 = h1 ∷ (∨ t1 (h2 ∷ t2))    
    ... | no ¬h1<h2 = h2 ∷ (∨ (h1 ∷ t1) t2)

    ∨-idem : (l : List Carrier) → ∨ l [] ≡ l
    ∨-idem [] = PE.refl
    ∨-idem (x ∷ l) = PE.refl

    ∨-All : {P : Carrier → Set} → (l1 l2 : List Carrier) → (All P l1) → (All P l2) → (All P (∨ l1 l2))
    ∨-All [] l2 p1 p2 = p2
    ∨-All (h1 ∷ t1) [] p1 p2 = p1
    ∨-All (h1 ∷ t1) (h2 ∷ t2) (ph1 ∷ pt1) (ph2 ∷ pt2) with h1 ∦? h2
    ... | l⊑r h1⊑h2 ¬h2⊑h1 = ∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2)
    ... | r⊑l ¬h1⊑h2 h2⊑h1 = ∨-All (h1 ∷ t1) t2 (ph1 ∷ pt1) pt2
    ... | l≡r h1≡h2 = ∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2)
    ... | l∥r h1∥h2 with h1 <? h2
    ... | yes h1<h2 = ph1 ∷ (∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2))
    ... | no ¬h1<h2 = ph2 ∷ (∨-All (h1 ∷ t1) t2 (ph1 ∷ pt1) pt2)

    ∨-Any : {P : Carrier → Set} → (l1 l2 : List Carrier) → ¬ (Any P l1) → ¬ (Any P l2) → ¬ (Any P (∨ l1 l2))
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

        goal : ¬ (Any P (h1 ∷ ∨ t1 (h2 ∷ t2)))
        goal (here px) = p1 (here px)
        goal (there z) = ∨-Any t1 (h2 ∷ t2) ¬Any-t1 p2 z
    ... | no ¬h1<h2 = goal h2 (h1 ∷ t1) t2 (λ ph2 → p2 $ here ph2) p1 (λ pt2 → p2 $ there pt2) 
      where
        ¬Any-t2 : ¬ (Any P t2)
        ¬Any-t2 any-t2 = p2 (there any-t2)

        -- I have to apply h t1 and t2 outside the where clause so that the termination metric registers
        goal : (h : Carrier) → (t1 t2 : List Carrier) → ¬ (P h) → ¬ (Any P t1) → ¬ (Any P t2) →  ¬ (Any P (h ∷ ∨ t1 t2))
        goal h t1 t2 a b c (here px) = a px --p2 (here px)
        goal h t1 t2 a b c (there z) = ∨-Any t1 t2 b c z  --∨-Any (h1 ∷ t1) t2 p1 ¬Any-t2 z

    -- todo: l ∨ k → IsFreeList l → IsFreeList k → IsFreeList l ∨ k
    ∨-free : (l1 l2 : List Carrier) → IsFreeList _<_ _⊑_ l1 → IsFreeList _<_ _⊑_ l2 → IsFreeList _<_ _⊑_ (∨ l1 l2)
    ∨-free [] l2 f1 f2 = f2
    ∨-free (h1 ∷ t1) [] f1 f2 = f1
    ∨-free (h1 ∷ t1) (h2 ∷ t2) f1@(∷-Free h1 t1 min1 incomp1 ft1) f2@(∷-Free h2 t2 min2 incomp2 ft2) with h1 ∦? h2
    ... | l⊑r h1⊑h2 ¬h2⊑h1  = ∨-free t1 (h2 ∷ t2) ft1 f2 
    ... | r⊑l ¬h1⊑h2 h2⊑h1 = ∨-free (h1 ∷ t1) t2 f1 ft2
    ... | l≡r h1≡h2 = ∨-free t1 (h2 ∷ t2) ft1 f2
    ... | l∥r h1∥h2 with h1 <? h2
    ... | yes h1<h2 = ∷-Free h1 (∨ t1 (h2 ∷ t2)) min incomp (∨-free t1 (h2 ∷ t2) ft1 f2) 
      where
        transitive : Transitive _<_
        transitive = IsStrictTotalOrder.trans isStrictTotalOrder 

        h1<t2 : All (h1 <_) t2
        h1<t2 = LA.map {P = h2 <_} {Q = h1 <_} (λ {x} → λ h2<x → transitive h1<h2 h2<x) min2

        min : All (h1 <_) (∨ t1 (h2 ∷ t2))
        min = ∨-All t1 (h2 ∷ t2) min1 (h1<h2 ∷ h1<t2)  

        incomp : ¬ (Any (λ x → h1 ∦ x) (∨ t1 (h2 ∷ t2)))
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
    ... | no ¬h1<h2 = ∷-Free h2 (∨ (h1 ∷ t1) t2) min incomp (∨-free (h1 ∷ t1) t2 f1 ft2)  
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

        min : All (h2 <_) (∨ (h1 ∷ t1) t2)
        min = ∨-All (h1 ∷ t1) t2 (h2<h1 ∷ h2<t1) min2  

        incomp : ¬ (Any (λ x → h2 ∦ x) (∨ (h1 ∷ t1) t2))
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
    
    h∷t≡h∨t : (h : Carrier) → (t : List Carrier) → (All (h <_) t) → ¬ (Any (h ∦_) t) → ((h ∷ t) ≡ (∨ Data.List.[ h ] t))
    h∷t≡h∨t h [] min incomp = PE.refl
    h∷t≡h∨t h (x ∷ t) min incomp with (h ∦? x) 
    h∷t≡h∨t h (x ∷ t) min incomp | l⊑r h⊑x ¬x⊑h = ⊥-elim $ incomp (here (inj₁ h⊑x))
    h∷t≡h∨t h (x ∷ t) min incomp | r⊑l ¬h⊑x x⊑h = ⊥-elim $ incomp (here (inj₂ x⊑h))
    h∷t≡h∨t h (x ∷ t) min incomp | l≡r h≡x = ⊥-elim $ incomp (here (inj₁ (reflexive h≡x)))
    h∷t≡h∨t h (x ∷ t) min incomp | l∥r h∥x with keep (h <? x) 
    ... | (yes h<x , s) rewrite s = PE.refl
    ... | (no ¬h<x , s) rewrite s = ⊥-elim $ ¬h<x (LA.head min)

    ∨-discardˡ : (h1 h2 : Carrier) → (t1 t2 : List Carrier) → (h1 ⊑ h2) →
                 (∨ (h1 ∷ t1) (h2 ∷ t2) ≡ ∨ t1 (h2 ∷ t2))
    ∨-discardˡ h1 h2 t1 t2 h1⊑h2 with h1 ∦? h2
    ∨-discardˡ h1 h2 t1 t2 h1⊑h2 | l⊑r _ ¬h2⊑h1 = PE.refl
    ∨-discardˡ h1 h2 t1 t2 h1⊑h2 | r⊑l ¬h1⊑h2 _ = ⊥-elim $ ¬h1⊑h2 h1⊑h2
    ∨-discardˡ h1 h2 t1 t2 h1⊑h2 | l≡r PE.refl = PE.refl
    ∨-discardˡ h1 h2 t1 t2 h1⊑h2 | l∥r h1∥h2 = ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)

    ∨-first : (h : Carrier) → (t l1 l2 : List Carrier) → (h ∷ t ≡ ∨ l1 l2) → (h ∈ l1 ⊎ h ∈ l2)
    ∨-first h t [] [] ()
    ∨-first h t [] (h2 ∷ t2) eq@PE.refl = inj₂ (here PE.refl)
    ∨-first h t (h1 ∷ t1) [] eq@PE.refl = inj₁ (here PE.refl)
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq with h1 ∦? h2
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | l⊑r h1⊑h2 ¬h2⊑h1 with (∨-first h t t1 (h2 ∷ t2) eq) 
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | l⊑r h1⊑h2 ¬h2⊑h1 | inj₁ h∈t1 = inj₁ (there h∈t1)
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | l⊑r h1⊑h2 ¬h2⊑h1 | inj₂ h∈h2∷t2 = inj₂ h∈h2∷t2 
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | r⊑l ¬h1⊑h2 h2⊑h1 with (∨-first h t (h1 ∷ t1) t2 eq) 
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | r⊑l ¬h1⊑h2 h2⊑h1 | inj₁ h∈h1∷t1 = inj₁ h∈h1∷t1
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | r⊑l ¬h1⊑h2 h2⊑h1 | inj₂ h∈t2 = inj₂ (there h∈t2)
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | l≡r h1≡h2@PE.refl with (∨-first h t t1 (h2 ∷ t2) eq) 
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | l≡r h1≡h2@PE.refl | inj₁ h∈t1 = inj₁ (there h∈t1)
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | l≡r h1≡h2@PE.refl | inj₂ h∈h2∷t2 = inj₂ h∈h2∷t2 
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | l∥r h1∥h2 with h1 <? h2
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | l∥r h1∥h2 | yes h1<h2 = inj₁ $ here (∷-injectiveˡ eq)
      where
        open import Data.List.Properties
    ∨-first h t (h1 ∷ t1) (h2 ∷ t2) eq | l∥r h1∥h2 | no ¬h1<h2 = inj₂ $ here (∷-injectiveˡ eq)
      where
        open import Data.List.Properties

    ∨-push : ∀ (h : Carrier) → (l1 l2 : List Carrier) → (All (h <_) l1) → ¬ (Any (h ∦_) l1) → (All (h <_) l2) → ¬ (Any (h ∦_) l2) → (h ∷ (∨ l1 l2) ≡ (∨ (h ∷ l1) l2))
    ∨-push h l1 [] min1 incomp1 min2 incomp2 rewrite (∨-idem l1) = PE.refl
    ∨-push h l1 (h2 ∷ l2) min1 incomp1 min2 incomp2 with h ∦? h2
    ∨-push h l1 (h2 ∷ l2) min1 incomp1 min2 incomp2 | l⊑r h⊑h2 ¬h2⊑h = ⊥-elim $ incomp2 (here $ inj₁ h⊑h2)
    ∨-push h l1 (h2 ∷ l2) min1 incomp1 min2 incomp2 | r⊑l ¬h⊑h2 h2⊑h = ⊥-elim $ incomp2 (here $ inj₂ h2⊑h)
    ∨-push h l1 (h2 ∷ l2) min1 incomp1 min2 incomp2 | l≡r h≡h2@PE.refl = ⊥-elim $ incomp2 (here $ inj₁ (reflexive PE.refl))
    ∨-push h l1 (h2 ∷ l2) min1 incomp1 min2 incomp2 | l∥r h∥h2 with h <? h2
    ∨-push h l1 (h2 ∷ l2) min1 incomp1 min2 incomp2 | l∥r h∥h2 | yes h<h2 = PE.refl
    ∨-push h l1 (h2 ∷ l2) min1 incomp1 min2 incomp2 | l∥r h∥h2 | no ¬h<h2 = ⊥-elim $ ¬h<h2 (head min2)

    ∨-comm : (l1 l2 : List Carrier) → IsFreeList _<_ _⊑_ l1 → IsFreeList _<_ _⊑_ l2 → (∨ l1 l2) ≡ (∨ l2 l1)
    ∨-comm [] k f1 f2 = PE.sym (∨-idem k)
    ∨-comm (h1 ∷ t1) [] f1 f2 = PE.refl
    ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 with h1 ∦? h2
    ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l⊑r h1⊑h2 ¬h2⊑h1 with h2 ∦? h1
    ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | l⊑r h1⊑h2 ¬h2⊑h1 | l⊑r h2⊑h1 ¬h1⊑h2 = ⊥-elim $ ¬h1⊑h2 h1⊑h2
    ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1@(∷-Free _ _ _ _ ft1) f2 | l⊑r h1⊑h2 ¬h2⊑h1 | DeltaPoset0.r⊑l x x₁ = ∨-comm t1 (h2 ∷ t2) ft1 f2
    ∨-comm (h1 ∷ t1) (.h1 ∷ t2) f1@(∷-Free _ _ min1 incomp1 ft1) f2@(∷-Free _ _ min2 incomp2 ft2) | l⊑r h1⊑h2 ¬h2⊑h1 | DeltaPoset0.l≡r h1≡h2@PE.refl = 
      begin
        ∨ t1 (h1 ∷ t2) ≡⟨ ∨-comm t1 (h1 ∷ t2) ft1 f2 ⟩
        ∨ (h1 ∷ t2) t1 ≡⟨ PE.sym $ ∨-push h1 t2 t1 min2 incomp2 min1 incomp1 ⟩
        h1 ∷ ∨ t2 t1 ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm t2 t1 ft2 ft1 ⟩
        h1 ∷ ∨ t1 t2 ≡⟨ ∨-push h1 t1 t2 min1 incomp1 min2 incomp2 ⟩
        ∨ (h1 ∷ t1) t2 ≡⟨ ∨-comm (h1 ∷ t1) t2 f1 ft2 ⟩
        ∨ t2 (h1 ∷ t1)
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
        ∨ t1 (h1 ∷ t2) ≡⟨ ∨-comm t1 (h1 ∷ t2) ft1 f2 ⟩
        ∨ (h1 ∷ t2) t1 ≡⟨ PE.sym $ ∨-push h1 t2 t1 min2 incomp2 min1 incomp1 ⟩
        h1 ∷ ∨ t2 t1 ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm t2 t1 ft2 ft1 ⟩
        h1 ∷ ∨ t1 t2 ≡⟨ ∨-push h1 t1 t2 min1 incomp1 min2 incomp2 ⟩
        ∨ (h1 ∷ t1) t2 ≡⟨ ∨-comm (h1 ∷ t1) t2 f1 ft2 ⟩
        ∨ t2 (h1 ∷ t1)
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
        h1 ∷ ∨ t1 (h1 ∷ t2) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm t1 (h1 ∷ t2) ft1 f2 ⟩
        h1 ∷ ∨ (h1 ∷ t2) t1 ≡⟨ PE.cong (λ x → h1 ∷ x) $ PE.sym (∨-push h1 t2 t1 min2 incomp2 min1 incomp1) ⟩
        h1 ∷ h1 ∷ ∨ t2 t1 ≡⟨ PE.cong (λ x → h1 ∷ h1 ∷ x) $ ∨-comm t2 t1 ft2 ft1 ⟩
        h1 ∷ h1 ∷ ∨ t1 t2 ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-push h1 t1 t2 min1 incomp1 min2 incomp2 ⟩
        h1 ∷ ∨ (h1 ∷ t1) t2 ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm (h1 ∷ t1) t2 f1 ft2 ⟩ 
        h1 ∷ ∨ t2 (h1 ∷ t1)
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
        h1 ∷ ∨ (h1 ∷ t1) t2 ≡⟨ PE.cong (λ x → h1 ∷ x) $ PE.sym (∨-push h1 t1 t2 min1 incomp1 min2 incomp2) ⟩
        h1 ∷ h1 ∷ ∨ t1 t2 ≡⟨ PE.cong (λ x → h1 ∷ h1 ∷ x) $ ∨-comm t1 t2 ft1 ft2 ⟩
        h1 ∷ h1 ∷ ∨ t2 t1 ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-push h1 t2 t1 min2 incomp2 min1 incomp1 ⟩
        h1 ∷ ∨ (h1 ∷ t2) t1
       ∎
      where
        open PE.≡-Reasoning

    ∨-discardʳ : {h1 h2 : Carrier} → {t1 t2 : List Carrier} → IsFreeList _<_ _⊑_ (h1 ∷ t1) → IsFreeList _<_ _⊑_ (h2 ∷ t2) → (h2 ⊑ h1) →
                 (∨ (h1 ∷ t1) (h2 ∷ t2) ≡ ∨ (h1 ∷ t1) t2)
    ∨-discardʳ {h1} {h2} {t1} {t2} f1 f2@(∷-Free _ _ _ _ ft2) h2⊑h1 =
      begin
        ∨ (h1 ∷ t1) (h2 ∷ t2) ≡⟨ ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 ⟩
        ∨ (h2 ∷ t2) (h1 ∷ t1) ≡⟨ ∨-discardˡ h2 h1 t2 t1 h2⊑h1  ⟩
        ∨ t2 (h1 ∷ t1) ≡⟨ ∨-comm t2 (h1 ∷ t1) ft2 f1 ⟩
        ∨ (h1 ∷ t1) t2
       ∎
      where
        open PE.≡-Reasoning

    incomp-lemma : {h1 h2 : Carrier} → {t2 : List Carrier} → (h1<h2 : h1 < h2) → (min2 : All (h2 <_) t2) → (h1∥h2 : h1 ∥ h2) → ¬ (Any (h1 ∦_) (h2 ∷ t2))
    incomp-lemma {h1} {h2} {t2} h1<h2 min2 h1∥h2 (here h1∦h2) = h1∥h2 h1∦h2
    incomp-lemma {h1} {h2} {t2} h1<h2 min2 h1∥h2 (there h1∦t2) = anyEliminate t2 eliminator h1∦t2 
           where
             eliminator : AnyEliminator Carrier ⊥ (h1 ∦_) t2
             eliminator a f h1∦a a∈t2 = (unimodality h1<h2 (LA.lookup min2 a∈t2) (∦-refl h1) h1∥h2) h1∦a

    mutual        
     ∨-assoc : (l1 l2 l3 : List Carrier) → IsFreeList _<_ _⊑_ l1 → IsFreeList _<_ _⊑_ l2 → IsFreeList _<_ _⊑_ l3 → (∨ l1 (∨ l2 l3)) ≡ (∨ (∨ l1 l2) l3)
     ∨-assoc [] l2 l3 f1 f2 f3 = PE.refl
     ∨-assoc (h1 ∷ t1) [] l3 f1 f2 f3 = PE.refl
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) [] f1 f2 f3 with h1 ∦? h2 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) [] f1 f2 f3 | l⊑r h1⊑h2 ¬h2⊑h1 rewrite (∨-idem $ ∨ t1 (h2 ∷ t2)) = PE.refl
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) [] f1 f2 f3 | r⊑l ¬h1⊑h2 h2⊑h1 rewrite (∨-idem $ ∨ (h1 ∷ t1) t2) = PE.refl
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) [] f1 f2 f3 | l≡r h1≡h2 rewrite (∨-idem $ ∨ t1 (h2 ∷ t2)) = PE.refl
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) [] f1 f2 f3 | l∥r h1∥h2 with h1 <? h2
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) [] f1 f2 f3 | l∥r h1∥h2 | yes h1<h2 = PE.refl
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) [] f1 f2 f3 | l∥r h1∥h2 | no ¬h1<h2 = PE.refl
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 with h1 ∦? h2 | h2 ∦? h3 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3 | l⊑r h1⊑h2 ¬h2⊑h1 | l⊑r h2⊑h3 ¬h3⊑h2 =
       begin
         ∨ (h1 ∷ t1) (∨ t2 (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ (h1 ∷ t1) x) $ ∨-comm t2 (h3 ∷ t3) ft2 f3 ⟩
         ∨ (h1 ∷ t1) (∨ (h3 ∷ t3) t2) ≡⟨ ∨-assoc (h1 ∷ t1) (h3 ∷ t3) t2 f1 f3 ft2 ⟩
         ∨ (∨ (h1 ∷ t1) (h3 ∷ t3)) t2 ≡⟨ PE.cong (λ x → ∨ x t2) $ ∨-discardˡ h1 h3 t1 t3 (transitive h1⊑h2 h2⊑h3) ⟩
         ∨ (∨ t1 (h3 ∷ t3)) t2 ≡⟨ PE.sym $ ∨-assoc t1 (h3 ∷ t3) t2 ft1 f3 ft2 ⟩
         ∨ t1 (∨ (h3 ∷ t3) t2) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) t2 f3 ft2 ⟩
         ∨ t1 (∨ t2 (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ PE.sym (∨-discardˡ h2 h3 t2 t3 h2⊑h3)  ⟩
         ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎ 
       where
         open PE.≡-Reasoning
         transitive : Transitive _⊑_
         transitive = IsDecPartialOrder.trans isDecPartialOrder 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 _ _ ft1) f2 f3@(∷-Free .h3 .t3 _ _ ft3) | l⊑r h1⊑h2 ¬h2⊑h1 | r⊑l ¬h2⊑h3 h3⊑h2 =
       begin
         ∨ (h1 ∷ t1) (∨ (h2 ∷ t2) t3) ≡⟨ ∨-assoc (h1 ∷ t1) (h2 ∷ t2) t3 f1 f2 ft3 ⟩
         ∨ (∨ (h1 ∷ t1) (h2 ∷ t2)) t3 ≡⟨ PE.cong (λ x → ∨ x t3) $ ∨-discardˡ h1 h2 t1 t2 h1⊑h2 ⟩
         ∨ (∨ t1 (h2 ∷ t2)) t3 ≡⟨ PE.sym $ ∨-assoc t1 (h2 ∷ t2) t3 ft1 f2 ft3 ⟩
         ∨ t1 (∨ (h2 ∷ t2) t3) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h2 ∷ t2) t3 f2 ft3  ⟩
         ∨ t1 (∨ t3 (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ PE.sym (∨-discardˡ h3 h2 t3 t2 h3⊑h2) ⟩
         ∨ t1 (∨ (h3 ∷ t3) (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) (h2 ∷ t2) f3 f2 ⟩ 
         ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩ 
         ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free _ _ _ _ ft1) f2@(∷-Free _ _ _ _ ft2) f3 | l⊑r h1⊑h2 ¬h2⊑h1 | l≡r PE.refl = 
       begin
         ∨ (h1 ∷ t1) (∨ t2 (h2 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ (h1 ∷ t1) x) $ ∨-comm t2 (h2 ∷ t3) ft2 f3 ⟩
         ∨ (h1 ∷ t1) (∨ (h2 ∷ t3) t2) ≡⟨ ∨-assoc (h1 ∷ t1) (h2 ∷ t3) t2 f1 f3 ft2 ⟩
         ∨ (∨ (h1 ∷ t1) (h2 ∷ t3)) t2 ≡⟨ PE.cong (λ x → ∨ x t2) $ ∨-discardˡ h1 h2 t1 t3 h1⊑h2 ⟩
         ∨ (∨ t1 (h2 ∷ t3)) t2 ≡⟨ PE.sym $ ∨-assoc t1 (h2 ∷ t3) t2 ft1 f3 ft2 ⟩
         ∨ t1 (∨ (h2 ∷ t3) t2) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h2 ∷ t3) t2 f3 ft2 ⟩
         ∨ t1 (∨ t2 (h2 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ PE.sym (∨-discardˡ h2 h2 t2 t3 (reflexive PE.refl)) ⟩
         ∨ t1 (∨ (h2 ∷ t2) (h2 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h2 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h2 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 with h2 <? h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free _ _ _ _ ft1) f2@(∷-Free _ _ min2 incomp2 ft2) f3@(∷-Free _ _ min3 incomp3 _) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 | yes h2<h3 =
       begin
          ∨ (h1 ∷ t1) (h2 ∷ ∨ t2 (h3 ∷ t3)) ≡⟨ ∨-discardˡ h1 h2 t1 (∨ t2 (h3 ∷ t3)) h1⊑h2 ⟩
          ∨ t1 (h2 ∷ ∨ t2 (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ h∷t≡h∨t h2 (∨ t2 (h3 ∷ t3)) p1 p2 ⟩
          ∨ t1 (∨ (h2 ∷ []) (∨ t2 (h3 ∷ t3))) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-assoc (h2 ∷ []) t2 (h3 ∷ t3) (∷-Free h2 [] [] (λ ()) []-Free) ft2 f3 ⟩
          ∨ t1 (∨ (∨ (h2 ∷ []) t2) (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ t1 (∨ x (h3 ∷ t3))) $ PE.sym (h∷t≡h∨t h2 t2 min2 incomp2) ⟩
          ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
          ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder
         
         p0 : All (h2 <_) (h3 ∷ t3)
         p0 = h2<h3 ∷ (LA.map (λ h3<x → (transitive h2<h3 h3<x)) min3)

         p1 : All (h2 <_) (∨ t2 (h3 ∷ t3))
         p1 = ∨-All t2 (h3 ∷ t3) min2 p0

         h2∥l3 : ¬ (Any (h2 ∦_) (h3 ∷ t3))
         h2∥l3 (here h2∦h3) = h2∥h3 h2∦h3
         h2∥l3 (there h2∦t3) = anyEliminate t3 eliminator h2∦t3
           where
             eliminator : AnyEliminator Carrier ⊥ (h2 ∦_) t3
             eliminator a f h2∦a a∈t3 = (unimodality h2<h3 (LA.lookup min3 a∈t3) (∦-refl h2) h2∥h3) h2∦a
         
         p2 : ¬ (Any (h2 ∦_) (∨ t2 (h3 ∷ t3)))
         p2 = ∨-Any t2 (h3 ∷ t3) incomp2 h2∥l3 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free _ _ _ _ ft1) f2@(∷-Free _ _ min2 incomp2 ft2) f3@(∷-Free _ _ min3 incomp3 _) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 | no ¬h2<h3 with h3<h2 | h1 ∦? h3 
       where
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder

         h3<h2 : h3 < h2
         h3<h2 with (compare h3 h2)
         h3<h2 | tri< goal _ _ = goal
         h3<h2 | tri≈ _ h3≡h2@PE.refl _ = ⊥-elim $ h2∥h3 (inj₁ (reflexive PE.refl)) 
         h3<h2 | tri> _ _ h2<h3 = ⊥-elim $ ¬h2<h3 h2<h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) (∷-Free .h1 .t1 _ _ ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 | no ¬h2<h3 | h3<h2 | l⊑r h1⊑h3 ¬h3⊑h1 = 
       begin
         ∨ t1 (h3 ∷ ∨ (h2 ∷ t2) t3) ≡⟨ PE.cong (λ x → ∨ t1 x) $ h∷t≡h∨t h3 (∨ (h2 ∷ t2) t3) p1 p2 ⟩
           ∨ t1 (∨ (h3 ∷ []) (∨ (h2 ∷ t2) t3)) ≡⟨ PE.cong (λ x → ∨ t1 (∨ (h3 ∷ []) x)) $ ∨-comm (h2 ∷ t2) t3 f2 ft3 ⟩
         -- How to solve: instead of using the awkward h∷t≡h∨t, we use a new lemma that says "h ∷ (∨ l1 l2) ≡ ∨ (h ∷ l1) l2" under the condition that h is min and incomp 
         ∨ t1 (∨ (h3 ∷ []) (∨ t3 (h2 ∷ t2))) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-assoc (h3 ∷ []) t3 (h2 ∷ t2) h3-free ft3 f2 ⟩
         ∨ t1 (∨ (∨ (h3 ∷ []) t3) (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 (∨ x (h2 ∷ t2))) $ (PE.sym (h∷t≡h∨t h3 t3 min3 incomp3)) ⟩
         ∨ t1 (∨ (h3 ∷ t3) (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) (h2 ∷ t2) f3 f2 ⟩
         ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder
         
         h3-free : IsFreeList _<_ _⊑_ (h3 ∷ [])
         h3-free = ∷-Free h3 [] [] (λ ()) []-Free

         p0 : All (h3 <_) (h2 ∷ t2)
         p0 = h3<h2 ∷ (LA.map (λ h2<x → (transitive h3<h2 h2<x)) min2)

         p1 : All (h3 <_) (∨ (h2 ∷ t2) t3)
         p1 = ∨-All (h2 ∷ t2) t3 p0 min3

         h3∥l2 : ¬ (Any (h3 ∦_) (h2 ∷ t2))
         h3∥l2 (here h3∦h2) = (∥-sym h2∥h3) h3∦h2
         h3∥l2 (there h3∦t2) = anyEliminate t2 eliminator h3∦t2
           where
             eliminator : AnyEliminator Carrier ⊥ (h3 ∦_) t2
             eliminator a f h3∦a a∈t2 = (unimodality h3<h2 (LA.lookup min2 a∈t2) (∦-refl h3) (∥-sym h2∥h3)) h3∦a
         
         p2 : ¬ (Any (h3 ∦_) (∨ (h2 ∷ t2) t3))
         p2 = ∨-Any (h2 ∷ t2) t3 h3∥l2 incomp3 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) (∷-Free .h1 .t1 _ _ ft1) (∷-Free .h2 .t2 min2 incomp2 ft2) (∷-Free .h3 .t3 min3 incomp3 _) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 | no ¬h2<h3 | h3<h2 | r⊑l ¬h1⊑h3 h3⊑h1 =
       ⊥-elim $ h2∥h3 (inj₂ h3⊑h2) 
       where
         transitive : Transitive _⊑_
         transitive = IsDecPartialOrder.trans isDecPartialOrder

         h3⊑h2 : h3 ⊑ h2
         h3⊑h2 = transitive h3⊑h1 h1⊑h2
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) (∷-Free .h1 .t1 _ _ ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 | no ¬h2<h3 | h3<h2 | l≡r h1≡h3@PE.refl =  
       begin
         ∨ t1 (h3 ∷ ∨ (h2 ∷ t2) t3) ≡⟨ PE.cong (λ x → ∨ t1 x) $ h∷t≡h∨t h3 (∨ (h2 ∷ t2) t3) p1 p2 ⟩
         ∨ t1 (∨ (h3 ∷ []) (∨ (h2 ∷ t2) t3)) ≡⟨ PE.cong (λ x → ∨ t1 (∨ (h3 ∷ []) x)) $ ∨-comm (h2 ∷ t2) t3 f2 ft3 ⟩
         ∨ t1 (∨ (h3 ∷ []) (∨ t3 (h2 ∷ t2))) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-assoc (h3 ∷ []) t3 (h2 ∷ t2) h3-free ft3 f2 ⟩
         ∨ t1 (∨ (∨ (h3 ∷ []) t3) (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 (∨ x (h2 ∷ t2))) $ (PE.sym (h∷t≡h∨t h3 t3 min3 incomp3)) ⟩
         ∨ t1 (∨ (h3 ∷ t3) (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) (h2 ∷ t2) f3 f2 ⟩
         ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder
         
         h3-free : IsFreeList _<_ _⊑_ (h3 ∷ [])
         h3-free = ∷-Free h3 [] [] (λ ()) []-Free

         p0 : All (h3 <_) (h2 ∷ t2)
         p0 = h3<h2 ∷ (LA.map (λ h2<x → (transitive h3<h2 h2<x)) min2)

         p1 : All (h3 <_) (∨ (h2 ∷ t2) t3)
         p1 = ∨-All (h2 ∷ t2) t3 p0 min3

         h3∥l2 : ¬ (Any (h3 ∦_) (h2 ∷ t2))
         h3∥l2 (here h3∦h2) = (∥-sym h2∥h3) h3∦h2
         h3∥l2 (there h3∦t2) = anyEliminate t2 eliminator h3∦t2
           where
             eliminator : AnyEliminator Carrier ⊥ (h3 ∦_) t2
             eliminator a f h3∦a a∈t2 = (unimodality h3<h2 (LA.lookup min2 a∈t2) (∦-refl h3) (∥-sym h2∥h3)) h3∦a
         
         p2 : ¬ (Any (h3 ∦_) (∨ (h2 ∷ t2) t3))
         p2 = ∨-Any (h2 ∷ t2) t3 h3∥l2 incomp3        
        
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) (∷-Free .h1 .t1 _ _ ft1) (∷-Free .h2 .t2 min2 incomp2 ft2) (∷-Free .h3 .t3 min3 incomp3 _) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 | no ¬h2<h3 | h3<h2 | l∥r h1∥h3 with h1 <? h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) (∷-Free .h1 .t1 _ _ ft1) (∷-Free .h2 .t2 min2 incomp2 ft2) (∷-Free .h3 .t3 min3 incomp3 _) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 | no ¬h2<h3 | h3<h2 | l∥r h1∥h3 | yes h1<h3 =
        ⊥-elim $ (unimodality h1<h3 h3<h2 (∦-refl h1) h1∥h3) (inj₁ h1⊑h2)
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 | no ¬h2<h3 | h3<h2 | l∥r h1∥h3 | no ¬h1<h3 with (compare h1 h3)
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) (∷-Free .h1 .t1 min1 incomp1 ft1) (∷-Free .h2 .t2 min2 incomp2 ft2) (∷-Free .h3 .t3 min3 incomp3 ft3) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 | no ¬h2<h3 | h3<h2 | DeltaPoset0.l∥r h1∥h3 | no ¬h1<h3 | tri< h1<h3 _ _ =
       ⊥-elim $ ¬h1<h3 h1<h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (.h1 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h1 .t3 min3 incomp3 ft3) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h1 | no ¬h2<h1 | h1<h2 | l∥r h1∥h3 | no ¬h1<h3 | tri≈ _ h1≡h3@PE.refl _ = 
       begin 
         h1 ∷ ∨ (h1 ∷ t1) (∨ (h2 ∷ t2) t3) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-assoc (h1 ∷ t1) (h2 ∷ t2) t3 f1 f2 ft3 ⟩
         h1 ∷ ∨ (∨ (h1 ∷ t1) (h2 ∷ t2)) t3 ≡⟨ PE.cong (λ x → h1 ∷ ∨ x t3) $ ∨-discardˡ h1 h2 t1 t2 h1⊑h2 ⟩
         h1 ∷ ∨ (∨ t1 (h2 ∷ t2)) t3 ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm (∨ t1 (h2 ∷ t2)) t3 (∨-free t1 (h2 ∷ t2) ft1 f2) ft3  ⟩
         h1 ∷ ∨ t3 (∨ t1 (h2 ∷ t2)) ≡⟨ ∨-push h1 t3 (∨ t1 (h2 ∷ t2)) min3 incomp3 min incomp  ⟩
         ∨ (h1 ∷ t3) (∨ t1 (h2 ∷ t2)) ≡⟨ ∨-comm (h1 ∷ t3) (∨ t1 (h2 ∷ t2)) f3 (∨-free t1 (h2 ∷ t2) ft1 f2) ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h1 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder
         
         min12 : All (h1 <_) (h2 ∷ t2)
         min12 = h1<h2 ∷ (LA.map (λ h2<x → transitive h1<h2 h2<x) min2)

         min : All (h1 <_) (∨ t1 (h2 ∷ t2))
         min = ∨-All t1 (h2 ∷ t2) min1 min12
         
         incomp12 : ¬ (Any (h1 ∦_) (h2 ∷ t2))
         incomp12 (here h1∦h2) = (∥-sym h2∥h1) h1∦h2
         incomp12 (there rest) = anyEliminate t2 eliminator rest 
           where
             eliminator : AnyEliminator Carrier ⊥ (h1 ∦_) t2
             eliminator a f h1∦a a∈t2 = (unimodality h1<h2 (LA.lookup min2 a∈t2) (inj₁ $ reflexive PE.refl) (∥-sym h2∥h1)) h1∦a

         incomp : ¬ (Any (h1 ∦_) (∨ t1 (h2 ∷ t2)))
         incomp = ∨-Any t1 (h2 ∷ t2) incomp1 incomp12  
         
         -- min13 = min3 

     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h3 | no ¬h2<h3 | h3<h2 | DeltaPoset0.l∥r h1∥h3 | no ¬h1<h3 | tri> _ _ h3<h1 =
       begin
         h3 ∷ ∨ (h1 ∷ t1) (∨ (h2 ∷ t2) t3) ≡⟨ PE.cong (λ x → h3 ∷ x) $ ∨-assoc (h1 ∷ t1) (h2 ∷ t2) t3 f1 f2 ft3 ⟩
         h3 ∷ ∨ (∨ (h1 ∷ t1) (h2 ∷ t2)) t3 ≡⟨ PE.cong (λ x → h3 ∷ ∨ x t3) $ ∨-discardˡ h1 h2 t1 t2 h1⊑h2 ⟩
         h3 ∷ ∨ (∨ t1 (h2 ∷ t2)) t3 ≡⟨ PE.cong (λ x → h3 ∷ x) $ ∨-comm (∨ t1 (h2 ∷ t2)) t3 (∨-free t1 (h2 ∷ t2) ft1 f2) ft3  ⟩
         h3 ∷ ∨ t3 (∨ t1 (h2 ∷ t2)) ≡⟨ ∨-push h3 t3 (∨ t1 (h2 ∷ t2)) min3 incomp3 min incomp ⟩
         ∨ (h3 ∷ t3) (∨ t1 (h2 ∷ t2)) ≡⟨ ∨-comm (h3 ∷ t3) (∨ t1 (h2 ∷ t2)) f3 (∨-free t1 (h2 ∷ t2) ft1 f2) ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎     
       where 
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder
         
         min31 : All (h3 <_) t1
         min31 = LA.map (λ h1<x → transitive h3<h1 h1<x) min1
         
         incomp31 : ¬ (Any (h3 ∦_) t1)
         incomp31 h3∦x = anyEliminate t1 eliminator h3∦x
           where
             eliminator : AnyEliminator Carrier ⊥ (h3 ∦_) t1
             eliminator a f h3∦a a∈t1 = (unimodality h3<h1 (LA.lookup min1 a∈t1) (∦-refl h3) (∥-sym h1∥h3)) h3∦a

         min32 : All (h3 <_) (h2 ∷ t2)
         min32 = h3<h2 ∷ (LA.map (λ h2<x → transitive h3<h2 h2<x) min2)

         min : All (h3 <_) (∨ t1 (h2 ∷ t2))
         min = ∨-All t1 (h2 ∷ t2) min31 min32
         
         incomp32 : ¬ (Any (h3 ∦_) (h2 ∷ t2))
         incomp32 (here h3∦h2) = (∥-sym h2∥h3) h3∦h2
         incomp32 (there rest) = anyEliminate t2 eliminator rest 
           where
             eliminator : AnyEliminator Carrier ⊥ (h3 ∦_) t2
             eliminator a f h3∦a a∈t2 = (unimodality h3<h2 (LA.lookup min2 a∈t2) (inj₁ $ reflexive PE.refl) (∥-sym h2∥h3)) h3∦a

         incomp : ¬ (Any (h3 ∦_) (∨ t1 (h2 ∷ t2)))
         incomp = ∨-Any t1 (h2 ∷ t2) incomp31 incomp32       
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | r⊑l x x₁ | q = {!!}
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free _ _ _ _ ft1) f2@(∷-Free _ _ _ _ ft2) f3 | l≡r PE.refl | l⊑r h2⊑h3 ¬h3⊑h2 =
       begin
         ∨ (h1 ∷ t1) (∨ t2 (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ (h1 ∷ t1) x) $ ∨-comm t2 (h3 ∷ t3) ft2 f3 ⟩
         ∨ (h1 ∷ t1) (∨ (h3 ∷ t3) t2) ≡⟨ ∨-assoc (h1 ∷ t1) (h3 ∷ t3) t2 f1 f3 ft2 ⟩
         ∨ (∨ (h1 ∷ t1) (h3 ∷ t3)) t2 ≡⟨ PE.cong (λ x → ∨ x t2) $ ∨-discardˡ h1 h3 t1 t3 h2⊑h3 ⟩
         ∨ (∨ t1 (h3 ∷ t3)) t2 ≡⟨ PE.sym $ ∨-assoc t1 (h3 ∷ t3) t2 ft1 f3 ft2 ⟩
         ∨ t1 (∨ (h3 ∷ t3) t2) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) t2 f3 ft2 ⟩
         ∨ t1 (∨ t2 (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ PE.sym (∨-discardˡ h1 h3 t2 t3 h2⊑h3) ⟩
         ∨ t1 (∨ (h1 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h1 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h1 ∷ t2)) (h3 ∷ t3) 
        ∎
       where
         open PE.≡-Reasoning
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free _ _ _ _ ft1) f2 f3@(∷-Free _ _ _ _ ft3) | l≡r PE.refl | r⊑l ¬h2⊑h3 h3⊑h2 = 
       begin
         ∨ (h1 ∷ t1) (∨ (h1 ∷ t2) t3) ≡⟨ ∨-assoc (h1 ∷ t1) (h1 ∷ t2) t3 f1 f2 ft3 ⟩
         ∨ (∨ (h1 ∷ t1) (h1 ∷ t2)) t3 ≡⟨ PE.cong (λ x → ∨ x t3) $ ∨-discardˡ h1 h1 t1 t2 (reflexive PE.refl) ⟩
         ∨ (∨ t1 (h1 ∷ t2)) t3 ≡⟨ PE.sym $ ∨-assoc t1 (h1 ∷ t2) t3 ft1 f2 ft3 ⟩
         ∨ t1 (∨ (h1 ∷ t2) t3) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h1 ∷ t2) t3 f2 ft3  ⟩
         ∨ t1 (∨ t3 (h1 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ PE.sym (∨-discardˡ h3 h1 t3 t2 h3⊑h2) ⟩
         ∨ t1 (∨ (h3 ∷ t3) (h1 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) (h1 ∷ t2) f3 f2 ⟩ 
         ∨ t1 (∨ (h1 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h1 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩ 
         ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free _ _ _ _ ft1) f2@(∷-Free _ _ _ _ ft2) f3 | l≡r PE.refl | l≡r PE.refl =
       begin
         ∨ (h1 ∷ t1) (∨ t2 (h1 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ (h1 ∷ t1) x) $ ∨-comm t2 (h1 ∷ t3) ft2 f3 ⟩
         ∨ (h1 ∷ t1) (∨ (h1 ∷ t3) t2) ≡⟨ ∨-assoc (h1 ∷ t1) (h1 ∷ t3) t2 f1 f3 ft2 ⟩
         ∨ (∨ (h1 ∷ t1) (h1 ∷ t3)) t2 ≡⟨ PE.cong (λ x → ∨ x t2) $ ∨-discardˡ h1 h1 t1 t3 (reflexive PE.refl) ⟩
         ∨ (∨ t1 (h1 ∷ t3)) t2 ≡⟨ PE.sym $ ∨-assoc t1 (h1 ∷ t3) t2 ft1 f3 ft2 ⟩
         ∨ t1 (∨ (h1 ∷ t3) t2) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h1 ∷ t3) t2 f3 ft2 ⟩
         ∨ t1 (∨ t2 (h1 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ PE.sym (∨-discardˡ h1 h1 t2 t3 (reflexive PE.refl)) ⟩
         ∨ t1 (∨ (h1 ∷ t2) (h1 ∷ t3)) ≡⟨ ∨-assoc t1 (h1 ∷ t2) (h1 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h1 ∷ t2)) (h1 ∷ t3) 
        ∎
       where
         open PE.≡-Reasoning
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l≡r PE.refl | l∥r h2∥h3 with h1 <? h3
     ∨-assoc (h1 ∷ t1) (.h1 ∷ t2) (h3 ∷ t3) f1@(∷-Free _ _ _ _ ft1) f2@(∷-Free .h1 t2 min2 incomp2 ft2) f3@(∷-Free _ _ min3 incomp3 _) | l≡r h1≡h2@PE.refl | l∥r h1∥h3 | yes h1<h3 =
       begin
          ∨ (h1 ∷ t1) (h1 ∷ ∨ t2 (h3 ∷ t3)) ≡⟨ ∨-discardˡ h1 h1 t1 (∨ t2 (h3 ∷ t3)) (reflexive PE.refl) ⟩
          ∨ t1 (h1 ∷ ∨ t2 (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-push h1 t2 (h3 ∷ t3) min2 incomp2 min13 h1∥l3  ⟩
          ∨ t1 (∨ (h1 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h1 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
          ∨ (∨ t1 (h1 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder
         
         min13 : All (h1 <_) (h3 ∷ t3)
         min13 = h1<h3 ∷ (LA.map (λ h3<x → (transitive h1<h3 h3<x)) min3)

         h1∥l3 : ¬ (Any (h1 ∦_) (h3 ∷ t3))
         h1∥l3 (here h1∦h3) = h1∥h3 h1∦h3
         h1∥l3 (there h1∦t3) = anyEliminate t3 eliminator h1∦t3
           where
             eliminator : AnyEliminator Carrier ⊥ (h1 ∦_) t3
             eliminator a f h1∦a a∈t3 = (unimodality h1<h3 (LA.lookup min3 a∈t3) (∦-refl h1) h1∥h3) h1∦a
   
     ∨-assoc (h1 ∷ t1) (.h1 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l≡r h1≡h2@PE.refl | l∥r h1∥h3 | no ¬h1<h3 with h3<h1 | h1 ∦? h3
       where
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder
     
         h3<h1 : h3 < h1
         h3<h1 with (compare h3 h1)
         h3<h1 | tri< goal _ _ = goal
         h3<h1 | tri≈ _ h3≡h1@PE.refl _ = ⊥-elim $ h1∥h3 (inj₁ (reflexive PE.refl)) 
         h3<h1 | tri> _ _ h1<h3 = ⊥-elim $ ¬h1<h3 h1<h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 _ _ ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l≡r h1≡h2@PE.refl | l∥r h1∥h3 | no ¬h1<h3 | h3<h1 | l⊑r h1⊑h3 ¬h3⊑h1 = 
       begin
         ∨ t1 (h3 ∷ ∨ (h1 ∷ t2) t3) ≡⟨ PE.cong (λ x → ∨ t1 (h3 ∷ x)) $ ∨-comm (h1 ∷ t2) t3 f2 ft3 ⟩
         ∨ t1 (h3 ∷ ∨ t3 (h1 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-push h3 t3 (h1 ∷ t2) min3 incomp3 min32 h3∥l2 ⟩
         ∨ t1 (∨ (h3 ∷ t3) (h1 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) (h2 ∷ t2) f3 f2 ⟩
         ∨ t1 (∨ (h1 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h1 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder
         
         min32 : All (h3 <_) (h1 ∷ t2)
         min32 = h3<h1 ∷ (LA.map (λ h1<x → (transitive h3<h1 h1<x)) min2)

         h3∥l2 : ¬ (Any (h3 ∦_) (h1 ∷ t2))
         h3∥l2 (here h3∦h1) = (∥-sym h1∥h3) h3∦h1
         h3∥l2 (there h3∦t2) = anyEliminate t2 eliminator h3∦t2
           where
             eliminator : AnyEliminator Carrier ⊥ (h3 ∦_) t2
             eliminator a f h3∦a a∈t2 = (unimodality h3<h1 (LA.lookup min2 a∈t2) (∦-refl h3) (∥-sym h1∥h3)) h3∦a
         
         p2 : ¬ (Any (h3 ∦_) (∨ (h1 ∷ t2) t3))
         p2 = ∨-Any (h2 ∷ t2) t3 h3∥l2 incomp3 
     ∨-assoc (h1 ∷ t1) (.h1 ∷ t2) (h3 ∷ t3) (∷-Free .h1 .t1 _ _ ft1) (∷-Free .h1 .t2 min2 incomp2 ft2) (∷-Free .h3 .t3 min3 incomp3 _) | l≡r h1≡h2@PE.refl | l∥r h1∥h3 | no ¬h1<h3 | h3<h1 | r⊑l ¬h1⊑h3 h3⊑h1 =
       ⊥-elim $ h1∥h3 (inj₂ h3⊑h1) 
     ∨-assoc (h1 ∷ t1) (.h1 ∷ t2) (h3 ∷ t3) (∷-Free .h1 .t1 _ _ ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l≡r h1≡h2@PE.refl | l∥r h1∥h3 | no ¬h1<h3 | h3<h1 | l≡r h1≡h3@PE.refl =  
       begin
         ∨ t1 (h3 ∷ ∨ (h1 ∷ t2) t3) ≡⟨ PE.cong (λ x → ∨ t1 x) $ h∷t≡h∨t h3 (∨ (h1 ∷ t2) t3) p1 p2 ⟩
         ∨ t1 (∨ (h3 ∷ []) (∨ (h1 ∷ t2) t3)) ≡⟨ PE.cong (λ x → ∨ t1 (∨ (h3 ∷ []) x)) $ ∨-comm (h1 ∷ t2) t3 f2 ft3 ⟩
         ∨ t1 (∨ (h3 ∷ []) (∨ t3 (h1 ∷ t2))) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-assoc (h3 ∷ []) t3 (h1 ∷ t2) h3-free ft3 f2 ⟩
         ∨ t1 (∨ (∨ (h3 ∷ []) t3) (h1 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 (∨ x (h1 ∷ t2))) $ (PE.sym (h∷t≡h∨t h3 t3 min3 incomp3)) ⟩
         ∨ t1 (∨ (h3 ∷ t3) (h1 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) (h1 ∷ t2) f3 f2 ⟩
         ∨ t1 (∨ (h1 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h1 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h1 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder
         
         h3-free : IsFreeList _<_ _⊑_ (h3 ∷ [])
         h3-free = ∷-Free h3 [] [] (λ ()) []-Free

         p0 : All (h3 <_) (h1 ∷ t2)
         p0 = h3<h1 ∷ (LA.map (λ h1<x → (transitive h3<h1 h1<x)) min2)

         p1 : All (h3 <_) (∨ (h1 ∷ t2) t3)
         p1 = ∨-All (h1 ∷ t2) t3 p0 min3

         h1∥l2 : ¬ (Any (h3 ∦_) (h1 ∷ t2))
         h1∥l2 (here h3∦h1) = (∥-sym h1∥h3) h3∦h1
         h1∥l2 (there h3∦t2) = anyEliminate t2 eliminator h3∦t2
           where
             eliminator : AnyEliminator Carrier ⊥ (h3 ∦_) t2
             eliminator a f h3∦a a∈t2 = (unimodality h3<h1 (LA.lookup min2 a∈t2) (∦-refl h3) (∥-sym h1∥h3)) h3∦a
         
         p2 : ¬ (Any (h3 ∦_) (∨ (h1 ∷ t2) t3))
         p2 = ∨-Any (h1 ∷ t2) t3 h1∥l2 incomp3       
     ∨-assoc (h1 ∷ t1) (.h1 ∷ t2) (h3 ∷ t3) (∷-Free .h1 .t1 _ _ ft1) (∷-Free .h1 .t2 min2 incomp2 ft2) (∷-Free .h3 .t3 min3 incomp3 _) | l≡r h1≡h2@PE.refl | l∥r h1∥h3 | no ¬h1<h3 | h3<h1 | l∥r _ with h1 <? h3
     ∨-assoc (h1 ∷ t1) (.h1 ∷ t2) (h3 ∷ t3) (∷-Free .h1 .t1 _ _ ft1) (∷-Free .h1 .t2 min2 incomp2 ft2) (∷-Free .h3 .t3 min3 incomp3 _) | l≡r h1≡h2@PE.refl | l∥r h1∥h3 | no ¬h1<h3 | h3<h1 | l∥r _ | yes h1<h3 = 
       ⊥-elim $ ¬h1<h3 h1<h3
     ∨-assoc (h1 ∷ t1) (.h1 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 _ ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l≡r h1≡h2@PE.refl | l∥r h1∥h3 | no _ | h3<h1 | l∥r _ | no ¬h1<h3 =
       begin
         h3 ∷ ∨ (h1 ∷ t1) (∨ (h1 ∷ t2) t3) ≡⟨ PE.cong (λ x → h3 ∷ x) $ ∨-assoc (h1 ∷ t1) (h1 ∷ t2) t3 f1 f2 ft3 ⟩
         h3 ∷ ∨ (∨ (h1 ∷ t1) (h1 ∷ t2)) t3 ≡⟨ PE.cong (λ x → h3 ∷ ∨ x t3) $ ∨-discardˡ h1 h1 t1 t2 (reflexive PE.refl) ⟩
         h3 ∷ ∨ (∨ t1 (h1 ∷ t2)) t3 ≡⟨ PE.cong (λ x → h3 ∷ x) $ ∨-comm (∨ t1 (h1 ∷ t2)) t3 (∨-free t1 (h1 ∷ t2) ft1 f2) ft3  ⟩
         h3 ∷ ∨ t3 (∨ t1 (h1 ∷ t2)) ≡⟨ ∨-push h3 t3 (∨ t1 (h1 ∷ t2)) min3 incomp3 min incomp ⟩
         ∨ (h3 ∷ t3) (∨ t1 (h1 ∷ t2)) ≡⟨ ∨-comm (h3 ∷ t3) (∨ t1 (h1 ∷ t2)) f3 (∨-free t1 (h1 ∷ t2) ft1 f2) ⟩
         ∨ (∨ t1 (h1 ∷ t2)) (h3 ∷ t3)
        ∎     
       where 
         open PE.≡-Reasoning
         transitive : Transitive _<_
         transitive = IsStrictTotalOrder.trans isStrictTotalOrder
         
         min31 : All (h3 <_) t1
         min31 = LA.map (λ h1<x → transitive h3<h1 h1<x) min1
         
         incomp31 : ¬ (Any (h3 ∦_) t1)
         incomp31 h3∦x = anyEliminate t1 eliminator h3∦x
           where
             eliminator : AnyEliminator Carrier ⊥ (h3 ∦_) t1
             eliminator a f h3∦a a∈t1 = (unimodality h3<h1 (LA.lookup min1 a∈t1) (∦-refl h3) (∥-sym h1∥h3)) h3∦a

         min32 : All (h3 <_) (h1 ∷ t2)
         min32 = h3<h1 ∷ (LA.map (λ h2<x → transitive h3<h1 h2<x) min2)

         min : All (h3 <_) (∨ t1 (h1 ∷ t2))
         min = ∨-All t1 (h1 ∷ t2) min31 min32
         
         incomp32 : ¬ (Any (h3 ∦_) (h1 ∷ t2))
         incomp32 (here h3∦h1) = (∥-sym h1∥h3) h3∦h1
         incomp32 (there rest) = anyEliminate t2 eliminator rest 
           where
             eliminator : AnyEliminator Carrier ⊥ (h3 ∦_) t2
             eliminator a f h3∦a a∈t2 = (unimodality h3<h1 (LA.lookup min2 a∈t2) (inj₁ $ reflexive PE.refl) (∥-sym h1∥h3)) h3∦a

         incomp : ¬ (Any (h3 ∦_) (∨ t1 (h1 ∷ t2)))
         incomp = ∨-Any t1 (h1 ∷ t2) incomp31 incomp32       

     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l⊑r h2⊑h3 ¬h3⊑h2 with h1 <? h2 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | p@(l⊑r h2⊑h3 ¬h3⊑h2) | yes h1<h2 with h1 ∦? h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free _ _ _ _ ft1) f2@(∷-Free _ _ _ _ ft2) f3 | l∥r h1∥h2 | l⊑r h2⊑h3 ¬h3⊑h2 | yes h1<h2 | l⊑r h1⊑h3 ¬h3⊑h1 = 
       begin
         ∨ (h1 ∷ t1) (∨ t2 (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ (h1 ∷ t1) x) $ ∨-comm t2 (h3 ∷ t3) ft2 f3 ⟩
         ∨ (h1 ∷ t1) (∨ (h3 ∷ t3) t2) ≡⟨ ∨-assoc (h1 ∷ t1) (h3 ∷ t3) t2 f1 f3 ft2 ⟩
         ∨ (∨ (h1 ∷ t1) (h3 ∷ t3)) t2 ≡⟨ PE.cong (λ x → ∨ x t2) $ ∨-discardˡ h1 h3 t1 t3 h1⊑h3 ⟩
         ∨ (∨ t1 (h3 ∷ t3)) t2 ≡⟨ PE.sym $ ∨-assoc t1 (h3 ∷ t3) t2 ft1 f3 ft2 ⟩
         ∨ t1 (∨ (h3 ∷ t3) t2) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) t2 f3 ft2 ⟩
         ∨ t1 (∨ t2 (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ PE.sym (∨-discardˡ h2 h3 t2 t3 h2⊑h3)  ⟩
         ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2@(∷-Free _ _ min2 incomp2 ft2) f3 | l∥r h1∥h2 | l⊑r h2⊑h3 ¬h3⊑h2 | no ¬h1<h2 =
       begin 
         ∨ (h1 ∷ t1) (∨ t2 (h3 ∷ t3)) ≡⟨ ∨-assoc (h1 ∷ t1) t2 (h3 ∷ t3) f1 ft2 f3 ⟩
         ∨ (∨ (h1 ∷ t1) t2) (h3 ∷ t3) ≡⟨ PE.sym $ ∨-discardˡ h2 h3 (∨ (h1 ∷ t1) t2) t3 h2⊑h3 ⟩
         ∨ (h2 ∷ (∨ (h1 ∷ t1) t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | r⊑l ¬h2⊑h3 h3⊑h2 with h1 <? h2
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3@(∷-Free _ _ _ _ ft3) | l∥r h1∥h2 | r⊑l ¬h2⊑h3 h3⊑h2 | yes h1<h2 with h1 ∦? h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 _ _ ft1) f2 f3@(∷-Free .h3 .t3 _ _ ft3) | DeltaPoset0.l∥r h1∥h2 | DeltaPoset0.r⊑l ¬h2⊑h3 h3⊑h2 | yes h1<h2 | l⊑r h1⊑h3 ¬h3⊑h1 =
       begin 
         ∨ (h1 ∷ t1) (∨ (h2 ∷ t2) t3) ≡⟨ ∨-assoc (h1 ∷ t1) (h2 ∷ t2) t3 f1 f2 ft3 ⟩
         ∨ (∨ (h1 ∷ t1) (h2 ∷ t2)) t3 ≡⟨ PE.cong (λ x → (∨ x t3)) $ ∨-discardˡ h1 h2 t1 t2 (transitive⊑ h1⊑h3 h3⊑h2) ⟩
         ∨ (∨ t1 (h2 ∷ t2)) t3 ≡⟨ PE.sym $ ∨-assoc t1 (h2 ∷ t2) t3 ft1 f2 ft3 ⟩
         ∨ t1 (∨ (h2 ∷ t2) t3) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h2 ∷ t2) t3 f2 ft3 ⟩
         ∨ t1 (∨ t3 (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ PE.sym (∨-discardˡ h3 h2 t3 t2 h3⊑h2) ⟩
         ∨ t1 (∨ (h3 ∷ t3) (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) (h2 ∷ t2) f3 f2 ⟩
         ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) (∷-Free .h3 .t3 _ _ ft3) | DeltaPoset0.l∥r h1∥h2 | DeltaPoset0.r⊑l ¬h2⊑h3 h3⊑h2 | yes h1<h2 | r⊑l ¬h1⊑h3 h3⊑h1 = 
       begin
         ∨ (h1 ∷ t1) (∨ (h2 ∷ t2) t3) ≡⟨ ∨-assoc (h1 ∷ t1) (h2 ∷ t2) t3 f1 f2 ft3 ⟩
         ∨ (∨ (h1 ∷ t1) (h2 ∷ t2)) t3 ≡⟨ PE.cong (λ x → ∨ x t3) $ PE.sym (∨-push h1 t1 (h2 ∷ t2) min1 incomp1 min12 incomp12) ⟩  
         ∨ (h1 ∷ ∨ t1 (h2 ∷ t2)) t3
        ∎
       where
         open PE.≡-Reasoning
         
         min12 : (All (h1 <_) (h2 ∷ t2))
         min12 = h1<h2 ∷ (LA.map (λ h2<x → transitive< h1<h2 h2<x) min2)

         incomp12 : ¬ (Any (h1 ∦_) (h2 ∷ t2))
         incomp12 (here h1∦h2) = h1∥h2 h1∦h2 
         incomp12 (there h1∦t2) = anyEliminate t2 eliminator h1∦t2
           where
             eliminator : AnyEliminator Carrier ⊥ (h1 ∦_) t2
             eliminator a f h1∦a a∈t2 = (unimodality h1<h2 (LA.lookup min2 a∈t2) (∦-refl h1) h1∥h2) h1∦a
 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (.h1 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h1 .t3 _ _ ft3) | DeltaPoset0.l∥r h1∥h2 | DeltaPoset0.r⊑l ¬h2⊑h1 h1⊑h2 | yes h1<h2 | l≡r h1≡h3@PE.refl =
       begin
         ∨ (h1 ∷ t1) (∨ (h2 ∷ t2) t3) ≡⟨ ∨-assoc (h1 ∷ t1) (h2 ∷ t2) t3 f1 f2 ft3 ⟩
         ∨ (∨ (h1 ∷ t1) (h2 ∷ t2)) t3 ≡⟨ PE.cong (λ x → ∨ x t3) $ ∨-discardˡ h1 h2 t1 t2 h1⊑h2 ⟩  
         ∨ (∨ t1 (h2 ∷ t2)) t3 ≡⟨ PE.sym $ ∨-assoc t1 (h2 ∷ t2) t3 ft1 f2 ft3 ⟩
         ∨ t1 (∨ (h2 ∷ t2) t3) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h2 ∷ t2) t3 f2 ft3 ⟩
         ∨ t1 (∨ t3 (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ PE.sym (∨-discardˡ h1 h2 t3 t2 h1⊑h2) ⟩
         ∨ t1 (∨ (h1 ∷ t3) (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h1 ∷ t3) (h2 ∷ t2) f3 f2 ⟩
         ∨ t1 (∨ (h2 ∷ t2) (h1 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h1 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h1 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 (∷-Free .h3 .t3 _ _ ft3) | DeltaPoset0.l∥r h1∥h2 | DeltaPoset0.r⊑l ¬h2⊑h3 h3⊑h2 | yes h1<h2 | l∥r h1∥h3 with h1 <? h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1)  f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | r⊑l ¬h2⊑h3 h3⊑h2 | yes h1<h2 | l∥r h1∥h3 | yes h1<h3 =
       begin --this is a good proof, I just need to  prove lemmas for the push in the where clause
         ∨ (h1 ∷ t1) (∨ (h2 ∷ t2) t3) ≡⟨ PE.sym $ ∨-push h1 t1 (∨ (h2 ∷ t2) t3) min1 incomp1 min123 incomp123 ⟩
         h1 ∷ ∨ t1 (∨ (h2 ∷ t2) t3)   ≡⟨ PE.cong (λ x → h1 ∷ ∨ t1 x) $ PE.sym (∨-discardʳ f2 f3 h3⊑h2)  ⟩
         h1 ∷ ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         h1 ∷ ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3) 
        ∎
       where
         open PE.≡-Reasoning

         min12 : (All (h1 <_) (h2 ∷ t2))
         min12 = h1<h2 ∷ (LA.map (λ h2<x → transitive< h1<h2 h2<x) min2)

         min13 : (All (h1 <_) t3)
         min13 = LA.map (λ h3<x → transitive< h1<h3 h3<x) min3 

         min123 : (All (h1 <_) (∨ (h2 ∷ t2) t3))
         min123 = ∨-All (h2 ∷ t2) t3 min12 min13

         incomp12 : ¬ (Any (h1 ∦_) (h2 ∷ t2))
         incomp12 (here h1∦h2) = h1∥h2 h1∦h2
         incomp12 (there h1∦t2) = anyEliminate t2 eliminator h1∦t2 
           where
             eliminator : AnyEliminator Carrier ⊥ (h1 ∦_) t2
             eliminator a f h1∦a a∈t2 = (unimodality h1<h2 (LA.lookup min2 a∈t2) (∦-refl h1) h1∥h2) h1∦a
         
         incomp13 : ¬ (Any (h1 ∦_) t3)
         incomp13 h1∦t3 = anyEliminate t3 eliminator h1∦t3 
           where
             eliminator : AnyEliminator Carrier ⊥ (h1 ∦_) t3
             eliminator a f h1∦a a∈t3 = (unimodality h1<h3 (LA.lookup min3 a∈t3) (∦-refl h1) h1∥h3) h1∦a
         
         incomp123 : ¬ (Any (h1 ∦_) (∨ (h2 ∷ t2) t3))
         incomp123 = ∨-Any (h2 ∷ t2) t3 incomp12 incomp13

     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 (∷-Free .h3 .t3 _ _ ft3) | l∥r h1∥h2 | r⊑l ¬h2⊑h3 h3⊑h2 | yes h1<h2 | l∥r h1∥h3 | no ¬h1<h3 =  
       ⊥-elim $ (unimodality h3<h1 h1<h2 (∦-refl h3) (∥-sym h1∥h3)) (inj₁ h3⊑h2) 
       where
         h3<h1 : h3 < h1 
         h3<h1 with compare h3 h1
         h3<h1 | tri< goal _ _ = goal 
         h3<h1 | tri≈ _ h3≡h1@PE.refl _ = ⊥-elim $ h1∥h3 (∦-refl h3)
         h3<h1 | tri> _ _ h1<h3 = ⊥-elim $ ¬h1<h3 h1<h3

         h3<h2 : h3 < h2
         h3<h2 = transitive< h3<h1 h1<h2

     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | r⊑l ¬h2⊑h3 h3⊑h2 | no ¬h1<h2 with h2 ∦? h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | r⊑l ¬h2⊑h3 h3⊑h2 | no ¬h1<h2 | l⊑r h2⊑h3 _ = ⊥-elim $ ¬h2⊑h3 h2⊑h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1)  f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | r⊑l ¬h2⊑h3 h3⊑h2 | no ¬h1<h2 | r⊑l _ _ =
       begin
         ∨ (h1 ∷ t1) (∨ (h2 ∷ t2) t3) ≡⟨ ∨-assoc (h1 ∷ t1) (h2 ∷ t2) t3 f1 f2 ft3 ⟩
         ∨ (∨ (h1 ∷ t1) (h2 ∷ t2)) t3 ≡⟨ PE.cong (λ x → ∨ x t3) $ ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 ⟩  
         ∨ (∨ (h2 ∷ t2) (h1 ∷ t1)) t3 ≡⟨ PE.cong (λ x → ∨ x t3) $ PE.sym (∨-push h2 t2 (h1 ∷ t1) min2 incomp2 min21 incomp21)  ⟩
         ∨ (h2 ∷ ∨ t2 (h1 ∷ t1)) t3 ≡⟨ PE.cong (λ x → ∨ (h2 ∷ x) t3) $ ∨-comm t2 (h1 ∷ t1) ft2 f1 ⟩
         ∨ (h2 ∷ ∨ (h1 ∷ t1) t2) t3
        ∎ 
       where
         open PE.≡-Reasoning
         h2<h1 : h2 < h1
         h2<h1 with compare h2 h1
         h2<h1 | tri< goal _ _ = goal
         h2<h1 | tri≈ _ h2≡h1@PE.refl _ = ⊥-elim $ h1∥h2 (inj₁ (reflexive PE.refl)) 
         h2<h1 | tri> _ _ h1<h2 = ⊥-elim $ ¬h1<h2 h1<h2
         
         min21 : All (h2 <_) (h1 ∷ t1)
         min21 = h2<h1 ∷ (LA.map (λ h1<x → transitive< h2<h1 h1<x) min1)
         
         incomp21 : ¬ (Any (h2 ∦_) (h1 ∷ t1))
         incomp21 (here h2∦h1) = ⊥-elim $ h1∥h2 (∦-sym h2∦h1)
         incomp21 (there h2∦t1) = anyEliminate t1 eliminator h2∦t1 
           where
             eliminator : AnyEliminator Carrier ⊥ (h2 ∦_) t1
             eliminator a f h2∦a a∈t1 = (unimodality h2<h1 (LA.lookup min1 a∈t1) (∦-refl h2) (∥-sym h1∥h2)) h2∦a
             
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | r⊑l ¬h2⊑h3 h3⊑h2 | no ¬h1<h2 | l≡r PE.refl =  ⊥-elim $ ¬h2⊑h3 (reflexive PE.refl) 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | r⊑l ¬h2⊑h3 h3⊑h2 | no ¬h1<h2 | l∥r h2∥h3 = ⊥-elim $ h2∥h3 (inj₂ h3⊑h2)
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (.h2 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l≡r h2≡h3@PE.refl with h1 <? h2 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (.h2 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h2 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | l≡r h2≡h3@PE.refl | yes h1<h2 =
       begin
         ∨ (h1 ∷ t1) (∨ t2 (h2 ∷ t3)) ≡⟨ PE.sym $ ∨-push h1 t1 (∨ t2 (h2 ∷ t3)) min1 incomp1 min123 incomp123 ⟩
         h1 ∷ (∨ t1 (∨ t2 (h2 ∷ t3))) ≡⟨ PE.cong (λ x → h1 ∷ ∨ t1 x) $ PE.sym (∨-discardˡ h2 h2 t2 t3 (reflexive PE.refl)) ⟩
         h1 ∷ ∨ t1 (∨ (h2 ∷ t2) (h2 ∷ t3)) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-assoc t1 (h2 ∷ t2) (h2 ∷ t3) ft1 f2 f3 ⟩
         h1 ∷ ∨ (∨ t1 (h2 ∷ t2)) (h2 ∷ t3) ≡⟨ ∨-push h1 (∨ t1 (h2 ∷ t2)) (h2 ∷ t3) min112 incomp112 min13 incomp13 ⟩ 
         ∨ (h1 ∷ ∨ t1 (h2 ∷ t2)) (h2 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         
         min13 : (All (h1 <_) (h2 ∷ t3))
         min13 = h1<h2 ∷ (LA.map (λ h2<x → transitive< h1<h2 h2<x) min3)

         min12 : (All (h1 <_) t2)
         min12 = LA.map (λ h3<x → transitive< h1<h2 h3<x) min2 

         min12' : (All (h1 <_) (h2 ∷ t2))
         min12' = h1<h2 ∷ min12

         min112 : (All (h1 <_) (∨ t1 (h2 ∷ t2)))
         min112 = ∨-All t1 (h2 ∷ t2) min1 min12'

         min123 : (All (h1 <_) (∨ t2 (h2 ∷ t3)))
         min123 = ∨-All t2 (h2 ∷ t3) min12 min13

         incomp13 : ¬ (Any (h1 ∦_) (h2 ∷ t3))
         incomp13 (here h1∦h2) = h1∥h2 h1∦h2
         incomp13 (there h1∦t3) = anyEliminate t3 eliminator h1∦t3 
           where
             eliminator : AnyEliminator Carrier ⊥ (h1 ∦_) t3
             eliminator a f h1∦a a∈t3 = (unimodality h1<h2 (LA.lookup min3 a∈t3) (∦-refl h1) h1∥h2) h1∦a
         
         incomp12 : ¬ (Any (h1 ∦_) t2)
         incomp12 h1∦t2 = anyEliminate t2 eliminator h1∦t2 
           where
             eliminator : AnyEliminator Carrier ⊥ (h1 ∦_) t2
             eliminator a f h1∦a a∈t2 = (unimodality h1<h2 (LA.lookup min2 a∈t2) (∦-refl h1) h1∥h2) h1∦a

         incomp12' : ¬ (Any (h1 ∦_) (h2 ∷ t2))
         incomp12' (here h1∦h2) = h1∥h2 h1∦h2
         incomp12' (there h1∦t2) = incomp12 h1∦t2

         incomp112 : ¬ (Any (h1 ∦_) (∨ t1 (h2 ∷ t2)))
         incomp112 = ∨-Any t1 (h2 ∷ t2) incomp1 incomp12'
 
         incomp123 : ¬ (Any (h1 ∦_) (∨ t2 (h2 ∷ t3)))
         incomp123 = ∨-Any t2 (h2 ∷ t3) incomp12 incomp13
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (.h2 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l≡r h2≡h3@PE.refl | no ¬h1<h2 with h2 <? h1
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (.h2 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h2 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | l≡r h2≡h3@PE.refl | no ¬h1<h2 | yes h2<h1 = 
       begin
         ∨ (h1 ∷ t1) (∨ t2 (h2 ∷ t3)) ≡⟨ ∨-assoc (h1 ∷ t1) t2 (h2 ∷ t3) f1 ft2 f3 ⟩
         ∨ (∨ (h1 ∷ t1) t2) (h2 ∷ t3) ≡⟨ PE.sym $ ∨-discardˡ h2 h2 (∨ (h1 ∷ t1) t2) t3 (reflexive PE.refl) ⟩
         ∨ (h2 ∷ (∨ (h1 ∷ t1) t2)) (h2 ∷ t3)
        ∎
        where
          open PE.≡-Reasoning
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (.h2 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l≡r h2≡h3@PE.refl | no ¬h1<h2 | no ¬h2<h1 =
       ⊥-elim contr
       where
         contr : ⊥
         contr with compare h1 h2
         contr | tri< h1<h2 _ _ = ¬h1<h2 h1<h2
         contr | tri≈ _ h1≡h2 _ = h1∥h2 (inj₁ $ reflexive h1≡h2) 
         contr | tri> _ _ h2<h1 = ¬h2<h1 h2<h1
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l∥r h2∥h3 with h1 <? h2 | h2 <? h3
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | yes h2<h3 with h1 ∦? h3 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | yes h2<h3 | l⊑r h1⊑h3 ¬h3⊑h1 = 
       ⊥-elim $ (unimodality h1<h2 h2<h3 (∦-refl h1) h1∥h2) (inj₁ h1⊑h3)
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | yes h2<h3 | r⊑l ¬h1⊑h3 h3⊑h1 = 
       -- same 
       ⊥-elim $ (unimodality h1<h2 h2<h3 (∦-refl h1) h1∥h2) (inj₂ h3⊑h1)
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | yes h2<h3 | l≡r h1≡h3 = 
       -- same
       ⊥-elim $ (unimodality h1<h2 h2<h3 (∦-refl h1) h1∥h2) (inj₁ (reflexive h1≡h3))
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | yes h2<h3 | l∥r h1∥h3 with h1 <? h3 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | yes h2<h3 | l∥r h1∥h3 | yes h1<h3 = 
       begin
         ∨ (h1 ∷ t1) (h2 ∷ ∨ t2 (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ (h1 ∷ t1) x) $ ∨-push h2 t2 (h3 ∷ t3) min2 incomp2 min23 incomp23  ⟩
         ∨ (h1 ∷ t1) (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ PE.sym $ ∨-push h1 t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) min1 incomp1 min123 incomp123  ⟩ 
         h1 ∷ ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3  ⟩ 
         h1 ∷ ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         min23 : All (h2 <_) (h3 ∷ t3)
         min23 = h2<h3 ∷ (LA.map (λ h3<x → transitive< h2<h3 h3<x) min3)

         incomp23 : ¬ (Any (h2 ∦_) (h3 ∷ t3))
         incomp23 (here h2∦h3) = h2∥h3 h2∦h3
         incomp23 (there h2∦t3) = anyEliminate t3 eliminator h2∦t3 
           where
             eliminator : AnyEliminator Carrier ⊥ (h2 ∦_) t3
             eliminator a f h2∦a a∈t3 = (unimodality h2<h3 (LA.lookup min3 a∈t3) (∦-refl h2) h2∥h3) h2∦a

         min12 : All (h1 <_) (h2 ∷ t2)
         min12 = h1<h2 ∷ LA.map (λ h3<x → transitive< h1<h2 h3<x) min2

         min13 : All (h1 <_) (h3 ∷ t3)
         min13 = h1<h3 ∷ LA.map (λ h3<x → transitive< h1<h3 h3<x) min3

         min123 : All (h1 <_) (∨ (h2 ∷ t2) (h3 ∷ t3))
         min123 = ∨-All (h2 ∷ t2) (h3 ∷ t3) min12 min13

         incomp12 : ¬ (Any (h1 ∦_) (h2 ∷ t2))
         incomp12 = incomp-lemma h1<h2 min2 h1∥h2

         incomp13 : ¬ (Any (h1 ∦_) (h3 ∷ t3))
         incomp13 = incomp-lemma h1<h3 min3 h1∥h3      

         incomp123 : ¬ (Any (h1 ∦_) (∨ (h2 ∷ t2) (h3 ∷ t3)))
         incomp123 = ∨-Any (h2 ∷ t2) (h3 ∷ t3) incomp12 incomp13
 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | yes h2<h3 | l∥r h1∥h3 | no ¬h1<h3 = ⊥-elim $ ¬h1<h3 (transitive< h1<h2 h2<h3)
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | no ¬h2<h3 with h3<h2 | h1 ∦? h3 
       where
         h3<h2 : h3 < h2
         h3<h2 with compare h2 h3
         h3<h2 | tri< h2<h3 _ _ = ⊥-elim $ ¬h2<h3 h2<h3 
         h3<h2 | tri≈ _ h2≡h3 _ = ⊥-elim $ h2∥h3 (inj₁ (reflexive h2≡h3))
         h3<h2 | tri> _ _ goal = goal
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | no ¬h2<h3 | h3<h2 | l⊑r h1⊑h3 ¬h3⊑h1 = 
       begin
         ∨ t1 (h3 ∷ ∨ (h2 ∷ t2) t3) ≡⟨ PE.cong (λ x → ∨ t1 (h3 ∷ x)) $ ∨-comm (h2 ∷ t2) t3 f2 ft3  ⟩
         ∨ t1 (h3 ∷ ∨ t3 (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-push h3 t3 (h2 ∷ t2) min3 incomp3 min32 incomp32 ⟩
         ∨ t1 (∨ (h3 ∷ t3) (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) (h2 ∷ t2) f3 f2 ⟩  
         ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         min32 : All (h3 <_) (h2 ∷ t2)
         min32 = h3<h2 ∷ LA.map (λ h2<x → transitive< h3<h2 h2<x) min2
 
         incomp32 : ¬ (Any (h3 ∦_) (h2 ∷ t2))
         incomp32 = incomp-lemma h3<h2 min2 (∥-sym h2∥h3)
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | no ¬h2<h3 | h3<h2 | r⊑l ¬h1⊑h3 h3⊑h1 =
       begin
         ∨ (h1 ∷ t1) (∨ (h2 ∷ t2) t3) ≡⟨ ∨-assoc (h1 ∷ t1) (h2 ∷ t2) t3 f1 f2 ft3 ⟩
         ∨ (∨ (h1 ∷ t1) (h2 ∷ t2)) t3 ≡⟨ PE.cong (λ x → ∨ x t3) $ PE.sym (∨-push h1 t1 (h2 ∷ t2) min1 incomp1 min12 incomp12) ⟩
         ∨ (h1 ∷ ∨ t1 (h2 ∷ t2)) t3
        ∎
       where
         open PE.≡-Reasoning
         min12 : All (h1 <_) (h2 ∷ t2)
         min12 = h1<h2 ∷ LA.map (λ h2<x → transitive< h1<h2 h2<x) min2

         incomp12 : ¬ (Any (h1 ∦_) (h2 ∷ t2))
         incomp12 = incomp-lemma h1<h2 min2 h1∥h2
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (.h1 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h1 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | l∥r h2∥h1 | yes h1<h2 | no ¬h2<h1 | _ | l≡r h1≡h3@PE.refl =
       begin
         ∨ t1 (h1 ∷ ∨ (h2 ∷ t2) t3) ≡⟨ PE.cong (λ x → ∨ t1 (h1 ∷ x)) $ ∨-comm (h2 ∷ t2) t3 f2 ft3 ⟩
         ∨ t1 (h1 ∷ ∨ t3 (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-push h1 t3 (h2 ∷ t2) min3 incomp3 min12 incomp12 ⟩
         ∨ t1 (∨ (h1 ∷ t3) (h2 ∷ t2)) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h1 ∷ t3) (h2 ∷ t2) f3 f2 ⟩
         ∨ t1 (∨ (h2 ∷ t2) (h1 ∷ t3)) ≡⟨ ∨-assoc t1 (h2 ∷ t2) (h1 ∷ t3) ft1 f2 f3 ⟩
         ∨ (∨ t1 (h2 ∷ t2)) (h1 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         min12 : All (h1 <_) (h2 ∷ t2)
         min12 = h1<h2 ∷ LA.map (λ h2<x → transitive< h1<h2 h2<x) min2

         incomp12 : ¬ (Any (h1 ∦_) (h2 ∷ t2))
         incomp12 = incomp-lemma h1<h2 min2 h1∥h2
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | no ¬h2<h3 | h3<h2 | l∥r h1∥h3 with h1 <? h3 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | no ¬h2<h3 | h3<h2 | l∥r h1∥h3 | yes h1<h3 = 
       begin
         h1 ∷ ∨ t1 (h3 ∷ ∨ (h2 ∷ t2) t3) ≡⟨ PE.cong (λ x → h1 ∷ ∨ t1 (h3 ∷ x)) $ ∨-comm (h2 ∷ t2) t3 f2 ft3  ⟩
         h1 ∷ ∨ t1 (h3 ∷ ∨ t3 (h2 ∷ t2)) ≡⟨ PE.cong (λ x → h1 ∷ ∨ t1 x) $ ∨-push h3 t3 (h2 ∷ t2) min3 incomp3 min32 incomp32 ⟩
         h1 ∷ ∨ t1 (∨ (h3 ∷ t3) (h2 ∷ t2)) ≡⟨ PE.cong (λ x → h1 ∷ ∨ t1 x) $ ∨-comm (h3 ∷ t3) (h2 ∷ t2) f3 f2 ⟩
         h1 ∷ ∨ t1 (∨ (h2 ∷ t2) (h3 ∷ t3)) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-assoc t1 (h2 ∷ t2) (h3 ∷ t3) ft1 f2 f3 ⟩
         h1 ∷ ∨ (∨ t1 (h2 ∷ t2)) (h3 ∷ t3)
        ∎
       where
         open PE.≡-Reasoning
         min32 : All (h3 <_) (h2 ∷ t2)
         min32 = h3<h2 ∷ LA.map (λ h2<x → transitive< h3<h2 h2<x) min2

         incomp32 : ¬ Any (h3 ∦_) (h2 ∷ t2)
         incomp32 = incomp-lemma h3<h2 min2 (∥-sym h2∥h3)
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) | l∥r h1∥h2 | l∥r h2∥h3 | yes h1<h2 | no ¬h2<h3 | h3<h2 | l∥r h1∥h3 | no ¬h1<h3 = {!!}
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l∥r h2∥h3 | no ¬h1<h2 | yes h2<h3 = {!!}
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1 f2 f3 | l∥r h1∥h2 | l∥r h2∥h3 | no ¬h1<h2 | no ¬h2<h3 = {!!} 
  
{-
Goal: ∨ (h1 ∷ t1) (∨ t2 (h2 ∷ t3)) ≡
      ∨ (h1 ∷ ∨ t1 (h2 ∷ t2)) (h2 ∷ t3)
-}
     {-    
    -- we will probably have to rewrite this using ∨ - read up on the Data.List.All and Data.List.Any modules, 
    -- finding any useful helper functions
    ∨-FP : Carrier-FP → Carrier-FP → Carrier-FP
    ∨-FP ([] , p1) (l2 , p2) = (l2 , p2)
    ∨-FP (x1 ∷ l1 , p1) ([] , p2) = (x1 ∷ l1 , p1)
    ∨-FP (x1 ∷ l1 , p1) (x2 ∷ l2 , p2) with x1 ∦? x2
    ∨-FP (x1 ∷ l1 , ∷-Free _ _ _ _ l1-free) (x2 ∷ l2 , p2) | yes (inj₁ _) = ∨-FP (l1 , l1-free) (x2 ∷ l2 , p2)
    ∨-FP (x1 ∷ l1 , p1) (x2 ∷ l2 , ∷-Free _ _ _ _ l2-free) | yes (inj₂ _) = ∨-FP (x1 ∷ l1 , p1) (l2 , l2-free)  
    ∨-FP (x1 ∷ l1 , p1@(∷-Free _ _ _ _ l1-free)) (x2 ∷ l2 , p2@(∷-Free _ _ _ _ l2-free)) | no ¬x1∦x2 with x1 <? x2
    ... | yes x1<x2 = {! ( x1 ∷ (∨-FP (l1 , l1-free) (x2 ∷ l2 , p2)) ,   )!}
      where
        --gotta prove that the result x1 ∷ proj₁ (∨-FP (l1 , l1-free) (x2 ∷ l2 , p2)) is a free list
        z : IsFreeList _<_ _⊑_ (x1 ∷ proj₁ (∨-FP (l1 , l1-free) (x2 ∷ l2 , p2)))
        z with proj₁ (∨-FP (l1 , l1-free) (x2 ∷ l2 , p2))
        ... | [] = ∷-Free x1 [] [] ¬any []-Free
          where 
            ¬any : ¬ Any (λ x → x1 ⊑ x ⊎ x ⊑ x1) []
            ¬any ()
        ... | hd ∷ rest = {!Free-∷ x1 (proj₁ (∨-FP (l1 , l1-free) (x2 ∷ l2 , p2))) !}
    ... | no ¬x1<x2 = {!!}

    ⊥-FP : Carrier-FP
    ⊥-FP = ( [] , []-Free )
    
    -}
    



    
