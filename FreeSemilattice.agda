module FreeSemilattice where

open import Function using (_$_)
open import Data.Empty
open import Data.List
open import Data.List.All as LA
open import Data.List.Any
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
    ∨ (h1 ∷ t1) (h2 ∷ t2) | yes (inj₁ _) = ∨ t1 (h2 ∷ t2)
    ∨ (h1 ∷ t1) (h2 ∷ t2) | yes (inj₂ _) = ∨ (h1 ∷ t1) t2  
    ∨ (h1 ∷ t1) (h2 ∷ t2) | no ¬h1∦h2 with h1 <? h2
    ... | yes h1<h2 = h1 ∷ (∨ t1 (h2 ∷ t2))    
    ... | no ¬h1<h2 = h2 ∷ (∨ (h1 ∷ t1) t2)

    ∨-idem : (l : List Carrier) → ∨ l [] ≡ l
    ∨-idem [] = PE.refl
    ∨-idem (x ∷ l) = PE.refl

    ∨-All : {P : Carrier → Set} → (l1 l2 : List Carrier) → (All P l1) → (All P l2) → (All P (∨ l1 l2))
    ∨-All [] l2 p1 p2 = p2
    ∨-All (h1 ∷ t1) [] p1 p2 = p1
    ∨-All (h1 ∷ t1) (h2 ∷ t2) (ph1 ∷ pt1) (ph2 ∷ pt2) with h1 ∦? h2
    ... | yes (inj₁ h1⊑h2) = ∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2)
    ... | yes (inj₂ h2⊑h1) = ∨-All (h1 ∷ t1) t2 (ph1 ∷ pt1) pt2
    ... | no h1∥h2 with h1 <? h2
    ... | yes h1<h2 = ph1 ∷ (∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2))
    ... | no ¬h1<h2 = ph2 ∷ (∨-All (h1 ∷ t1) t2 (ph1 ∷ pt1) pt2)

    ∨-Any : {P : Carrier → Set} → (l1 l2 : List Carrier) → ¬ (Any P l1) → ¬ (Any P l2) → ¬ (Any P (∨ l1 l2))
    ∨-Any {P} [] l2 p1 p2 = p2
    ∨-Any {P} (h1 ∷ t1) [] p1 p2 = p1
    ∨-Any {P} (h1 ∷ t1) (h2 ∷ t2) p1 p2 with (h1 ∦? h2)
    ... | yes (inj₁ h1⊑h2) = ∨-Any t1 (h2 ∷ t2) ¬Any-t1 p2 
      where
        ¬Any-t1 : ¬ (Any P t1)
        ¬Any-t1 any-t1 = p1 (there any-t1)
    ... | yes (inj₂ h2⊑h1) = ∨-Any (h1 ∷ t1) t2 p1 ¬Any-t2 
      where
        ¬Any-t2 : ¬ (Any P t2)
        ¬Any-t2 any-t2 = p2 (there any-t2)
    ... | no h1∥h2 with h1 <? h2
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
    ... | yes (inj₁ h1⊑h2) = ∨-free t1 (h2 ∷ t2) ft1 f2 
    ... | yes (inj₂ h2⊑h1) = ∨-free (h1 ∷ t1) t2 f1 ft2
    ... | no h1∥h2 with h1 <? h2
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
    h∷t≡h∨t h (x ∷ t) min incomp | yes p = ⊥-elim $ incomp (here p)
    h∷t≡h∨t h (x ∷ t) min incomp | no h∥x with keep (h <? x) 
    ... | (yes h<x , s) rewrite s = PE.refl
    ... | (no ¬h<x , s) rewrite s = ⊥-elim $ ¬h<x (LA.head min)

    ∨-discard : (h1 h2 : Carrier) → (t1 t2 : List Carrier) → (h1 ⊑ h2) → ¬ (h2 ⊑ h1) →
                 (∨ (h1 ∷ t1) (h2 ∷ t2) ≡ ∨ t1 (h2 ∷ t2))
    ∨-discard h1 h2 t1 t2 h1⊑h2 ¬h2⊑h1 with h1 ∦? h2
    ∨-discard h1 h2 t1 t2 h1⊑h2 ¬h2⊑h1 | yes (inj₁ _) = PE.refl
    ∨-discard h1 h2 t1 t2 h1⊑h2 ¬h2⊑h1 | yes (inj₂ h2⊑h1) = {!⊥-elim $ ¬h2⊑h1 h2⊑h1!} -- PE.sym $ h∷t≡h∨t h2 t2 min2 incomp2
    ∨-discard h1 h2 t1 t2 h1⊑h2 ¬h2⊑h1 | no h1∥h2 = ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)

--    ∨-discard h1 h2 (t1h ∷ t1t) t2 h1⊑h2 f1 f2 with h1 ∦? h2
--    ∨-discard h1 h2 (t1h ∷ t1t) t2 h1⊑h2 f1 f2 | yes (inj₁ _) = PE.refl
--    ∨-discard h1 h2 (t1h ∷ t1t) t2 h1⊑h2 (∷-Free .h1 .(t1h ∷ t1t) min1 incomp1 ft1) f2 | yes (inj₂ h2⊑h1) rewrite (antisym h2⊑h1 h1⊑h2) with t1h ∦? h1
--    ∨-discard h1 h2 (t1h ∷ t1t) [] h1⊑h2 (∷-Free .h1 .(t1h ∷ t1t) min1 incomp1 ft1) f2 | yes (inj₂ h2⊑h1) | yes (inj₁ t1h⊑h1) = ⊥-elim $ incomp1 (here (inj₂ t1h⊑h1))
--    ∨-discard h1 h2 (t1h ∷ t1t) (t2h ∷ t2t) h1⊑h2 _ f2 | yes (inj₂ h2⊑h1) | yes (inj₁ h1⊑th1) rewrite (antisym h2⊑h1 h1⊑h2) with h2 ∦? t2h
--    ∨-discard h1 h2 (t1h ∷ t1t) (t2h ∷ t2t) h1⊑h2 (∷-Free _ _ _ _ ft1) (∷-Free _ _ _ _ ft2) | yes (inj₂ h2⊑h1) | yes (inj₁ t1h⊑h1) | yes (inj₁ h2⊑t2h) = {!∨-discard t1h t2h t1t t2t ft1 ft2!}
    

  -- []-Free : IsFreeList _<_ _⊑_ []
  -- ∷-Free : (hd : A) → (tl : List A) → (All (hd <_) tl) → ¬ (Any (λ x → (hd ⊑ x) ⊎ (x ⊑ hd)) tl) → 
 --           (IsFreeList _<_ _⊑_ tl) → IsFreeList _<_ _⊑_ (hd ∷ tl) 
    -- ∨-discard h1 h2 [] t2 h1⊑h2 min1 incomp1 min2 incomp2 | no h1∥h2 | yes h1<h2 = {!!}


    --rewrite (antisym h1⊑h2 h2⊑h1) = PE.sym $ h∷t≡h∨t h2 t2 min2 incomp2
    --∨-discard h1 h2 (t1h ∷ t1t) t2 h1⊑h2 min1 incomp1 min2 incomp2 with h1 ∦? h2
    --∨-discard h1 h2 (t1h ∷ t1t) t2 h1⊑h2 min1 incomp1 min2 incomp2 | yes (inj₁ _) = PE.refl
    --∨-discard h1 h2 (t1h ∷ t1t) t2 h1⊑h2 min1 incomp1 min2 incomp2 | yes (inj₂ h2⊑h1) rewrite (antisym h2⊑h1 h1⊑h2) with t1h ∦? h1
    --∨-discard h1 h2 (t1h ∷ t1t) [] h1⊑h2 min1 incomp1 min2 incomp2 | yes (inj₂ h2⊑h1) | yes (inj₁ t1h⊑h1) = {!!}
    --∨-discard h1 h2 (t1h ∷ t1t) (x ∷ t2) h1⊑h2 min1 incomp1 min2 incomp2 | yes (inj₂ h2⊑h1) | yes (inj₁ t1h⊑h1) = {!!}

    --with h1 ∦? h2
    --... | yes (inj₁ _) =  PE.refl
    --... | yes (inj₂ h2⊑h1) rewrite (antisym h1⊑h2 h2⊑h1)
    --... | no  h1∥h2 = {!!}

 
    mutual
     ∨-assoc : (l1 l2 l3 : List Carrier) → IsFreeList _<_ _⊑_ l1 → IsFreeList _<_ _⊑_ l2 → IsFreeList _<_ _⊑_ l3 → (∨ l1 (∨ l2 l3)) ≡ (∨ (∨ l1 l2) l3)
     ∨-assoc [] l2 l3 f1 f2 f3 = PE.refl
     ∨-assoc (h1 ∷ t1) [] l3 f1 f2 f3 = PE.refl
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) [] f1 f2 f3 with h1 ∦? h2 
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) [] f1 f2 f3 | yes (inj₁ h1⊑h2) rewrite (∨-idem $ ∨ t1 (h2 ∷ t2)) = PE.refl
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) [] f1 f2 f3 | yes (inj₂ h2⊑h1) rewrite (∨-idem $ ∨ (h1 ∷ t1) t2) = PE.refl
     ∨-assoc (h1 ∷ t1) (h2 ∷ t2) (h3 ∷ t3) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) f3@(∷-Free .h3 .t3 min3 incomp3 ft3) with h1 ∦? h2 | h2 ∦? h3
     ... | yes (inj₁ h1⊑h2) | yes (inj₁ h2⊑h3) = {!!} -- with p | keep (h1 ∦? h3)
       where
         open ≡-Reasoning
         transitive : Transitive _⊑_
         transitive = IsDecPartialOrder.trans isDecPartialOrder 
         
         p1 : (∨ (h1 ∷ t1) (h3 ∷ t3)) ≡ (∨ t1 (h3 ∷ t3))
         p1 with h1 ∦? h3
         p1 | yes (inj₁ h1⊑h3) = PE.refl  
         p1 | yes (inj₂ h3⊑h1) with h1≡h3
           where
             h1≡h3 : h1 ≡ h3
             h1≡h3 = antisym (transitive h1⊑h2 h2⊑h3) h3⊑h1
         ... | PE.refl = {!!} 
         p : ∨ (h1 ∷ t1) (∨ t2 (h3 ∷ t3)) ≡ ∨ (∨ (h1 ∷ t1) (h3 ∷ t3)) t2
         p = begin
               ∨ (h1 ∷ t1) (∨ t2 (h3 ∷ t3)) ≡⟨ PE.cong (λ x → ∨ (h1 ∷ t1) x) $ ∨-comm t2 (h3 ∷ t3) ft2 f3 ⟩
               ∨ (h1 ∷ t1) (∨ (h3 ∷ t3) t2) ≡⟨ ∨-assoc (h1 ∷ t1) (h3 ∷ t3) t2 f1 f3 ft2 ⟩
               ∨ (∨ (h1 ∷ t1) (h3 ∷ t3)) t2
              ∎
         
  
        -- ∨ (∨ t1 (h3 ∷ t3)) t2 ≡⟨ ∨-assoc t1 (h3 ∷ t3) t2 f1 f3 ft2 ⟩
        -- ∨ t1 (∨ (h3 ∷ t3) t2) ≡⟨ PE.cong (λ x → ∨ t1 x) $ ∨-comm (h3 ∷ t3) t2 f3 ft2 ⟩
        -- ∨ t1 (∨ t2 (h3 ∷ t3))
         
     ∨-comm : (l1 l2 : List Carrier) → IsFreeList _<_ _⊑_ l1 → IsFreeList _<_ _⊑_ l2 → (∨ l1 l2) ≡ (∨ l2 l1)
     ∨-comm [] k f1 f2 = PE.sym (∨-idem k)
     ∨-comm (h1 ∷ t1) [] f1 f2 = PE.refl
     ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 with h1 ∦? h2 | h2 ∦? h1
     ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) | yes (inj₁ h1⊑h2) | yes (inj₂ _) =
       ∨-comm t1 (h2 ∷ t2) ft1 f2
     ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) | yes (inj₂ h2⊑h1) | yes (inj₁ _) =
       ∨-comm (h1 ∷ t1) t2 f1 ft2
     ∨-comm (h1 ∷ t1) (h2 ∷ t2) f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) | yes (inj₁ h1⊑h2) | yes (inj₁ h2⊑h1) =
       {!!}
       where 
         h1≡h2 : h1 ≡ h2
         h1≡h2 = antisym h1⊑h2 h2⊑h1
         
         goal : ∨ t1 (h2 ∷ t2) ≡ ∨ t2 (h1 ∷ t1)
         goal with h1≡h2
         goal | refl = {!!}
        
      --begin
      --  ∨ t1 (h2 ∷ t2) ≡⟨ ∨-comm t1 (h2 ∷ t2) ft1 f2 ⟩
      --  ∨ (h2 ∷ t2) t1 ≡⟨ {!PE.refl!} ⟩
      --  ∨ (h1 ∷ t1) t2 ≡⟨ {!!} ⟩
      --  ∨ t2 (h1 ∷ t1)
      -- ∎
      -- where
      --  open PE.≡-Reasoning
      --  p : ∨ (h2 ∷ t2) t1 ≡ ∨ (h2 ∷ t2) (h1 ∷ t1)
      --  p with h2 ⊑? h1
      --  p | yes h2⊑h1 = {!!}
      --  p | no ¬h2⊑h1 = {!!}
    -- ∨-comm (hl ∷ tl) (hk ∷ tk) f1 f2 | (yes (inj₂ y) , s) rewrite s = {!!}
    -- ∨-comm (hl ∷ tl) (hk ∷ tk) f1 f2 | (no ¬p , s) rewrite s = {!!}

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

    



    
