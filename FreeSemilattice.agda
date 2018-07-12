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

    -- todo:
    -- lemma: l ∨ k = k ∨ l
    -- it's not hard to see that commutativity of ∨ doesn't hold w/o the free list property
    --∨-comm : (l1 l2 : List Carrier) → IsFreeList _<_ _⊑_ l1 → IsFreeList _<_ _⊑_ l2 → (∨ l1 l2) ≡ (∨ l2 l1)
    --∨-comm [] k f1 f2 = PE.sym (∨-idem k)
    --∨-comm (h1 ∷ t1) [] f1 f2 = PE.refl
    --∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 with (h1 ∦? h2)
    --∨-comm (h1 ∷ t1) (h2 ∷ t2) f1 f2 | yes (inj₁ h1⊑h2) =
    --  begin
    --    ∨ t1 (h2 ∷ t2) ≡⟨ ∨-comm t1 (h2 ∷ t2) ⟩
    --    ∨ (h2 ∷ t2) t1 ≡⟨ {!!} ⟩
    --    ∨ (h2 ∷ t2) (h1 ∷ t1)
    --   ∎
    --  where
    --    open PE.≡-Reasoning
    --    p : ∨ (h2 ∷ t2) t1 ≡ ∨ (h2 ∷ t2) (h1 ∷ t1)
    --    p with h2 ⊑? h1
    --    p | yes h2⊑h1 = {!!}
    --    p | no ¬h2⊑h1 = {!!}

    -- ∨-comm (hl ∷ tl) (hk ∷ tk) f1 f2 | yes (inj₂ y) = {!!}
    -- ∨-comm (hl ∷ tl) (hk ∷ tk) f1 f2 | no ¬p = {!!}
    

    ∨-All : {P : Carrier → Set} → (l1 l2 : List Carrier) → (All P l1) → (All P l2) → (All P (∨ l1 l2))
    ∨-All [] l2 p1 p2 = p2
    ∨-All (h1 ∷ t1) [] p1 p2 = p1
    ∨-All (h1 ∷ t1) (h2 ∷ t2) (ph1 ∷ pt1) (ph2 ∷ pt2) with keep (h1 ∦? h2)
    ... | yes (inj₁ h1⊑h2) , q rewrite q = ∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2)
    ... | yes (inj₂ h2⊑h1) , q rewrite q = ∨-All (h1 ∷ t1) t2 (ph1 ∷ pt1) pt2
    ... | no h1∥h2 , q with keep (h1 <? h2)
    ... | yes h1<h2 , r rewrite q | r = ph1 ∷ (∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2))
    ... | no ¬h1<h2 , r rewrite q | r = ph2 ∷ (∨-All (h1 ∷ t1) t2 (ph1 ∷ pt1) pt2)

    ∨-Any : {P : Carrier → Set} → (l1 l2 : List Carrier) → ¬ (Any P l1) → ¬ (Any P l2) → ¬ (Any P (∨ l1 l2))
    ∨-Any {P} [] l2 p1 p2 = p2
    ∨-Any {P} (h1 ∷ t1) [] p1 p2 = p1
    ∨-Any {P} (h1 ∷ t1) (h2 ∷ t2) p1 p2 with keep (h1 ∦? h2)
    ... | yes (inj₁ h1⊑h2) , q rewrite q = ∨-Any t1 (h2 ∷ t2) ¬Any-t1 p2 
      where
        ¬Any-t1 : ¬ (Any P t1)
        ¬Any-t1 any-t1 = p1 (there any-t1)
    ... | yes (inj₂ h2⊑h1) , q rewrite q = ∨-Any (h1 ∷ t1) t2 p1 ¬Any-t2 
      where
        ¬Any-t2 : ¬ (Any P t2)
        ¬Any-t2 any-t2 = p2 (there any-t2)
    ... | no h1∥h2 , q with keep (h1 <? h2)
    ... | yes h1<h2 , r rewrite q | r = goal
      where 
        ¬Any-t1 : ¬ (Any P t1)
        ¬Any-t1 any-t1 = p1 (there any-t1)

        goal : ¬ (Any P (h1 ∷ ∨ t1 (h2 ∷ t2)))
        goal (here px) = p1 (here px)
        goal (there z) = ∨-Any t1 (h2 ∷ t2) ¬Any-t1 p2 z
    ... | no ¬h1<h2 , r rewrite q | r = goal h2 (h1 ∷ t1) t2 (λ ph2 → p2 $ here ph2) p1 (λ pt2 → p2 $ there pt2) 
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
    ∨-free (h1 ∷ t1) (h2 ∷ t2) f1@(∷-Free h1 t1 min1 incomp1 ft1) f2@(∷-Free h2 t2 min2 incomp2 ft2) with keep (h1 ∦? h2)
    ... | yes (inj₁ h1⊑h2) , q rewrite q = ∨-free t1 (h2 ∷ t2) ft1 f2 
    ... | yes (inj₂ h2⊑h1) , q rewrite q = ∨-free (h1 ∷ t1) t2 f1 ft2
    ... | no h1∥h2 , q with keep (h1 <? h2)
    ... | yes h1<h2 , r rewrite q | r = ∷-Free h1 (∨ t1 (h2 ∷ t2)) min incomp (∨-free t1 (h2 ∷ t2) ft1 f2) 
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
    ... | no ¬h1<h2 , r rewrite q | r = {!∷-Free h2 (∨ (h1 ∷ t1) t2) min incomp (∨-free (h1 ∷ t1) t2 f1 ft2) !} 
      where
        transitive : Transitive _<_
        transitive = IsStrictTotalOrder.trans isStrictTotalOrder 

        total : Trichotomous _≈_ _<_
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

    -- lemma: (All P l) → (All P k) → (All P (∨ l k)) 
    -- lemma: ¬ (Any P l) → ¬ (Any P k) → ¬ (Any P (∨ l k))
    
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

    



    
