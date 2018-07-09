module FreeSemilattice where

open import Function using (_$_)
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
    ... | no ¬h1⊑h2 , q with keep (h1 <? h2)
    ... | yes h1<h2 , r rewrite q | r = ph1 ∷ (∨-All t1 (h2 ∷ t2) pt1 (ph2 ∷ pt2))
    ... | no ¬h1<h2 , r rewrite q | r = ph2 ∷ (∨-All (h1 ∷ t1) t2 (ph1 ∷ pt1) pt2)

    -- todo: l ∨ k → IsFreeList l → IsFreeList k → IsFreeList l ∨ k
    ∨-free : (l1 l2 : List Carrier) → IsFreeList _<_ _⊑_ l1 → IsFreeList _<_ _⊑_ l2 → IsFreeList _<_ _⊑_ (∨ l1 l2)
    ∨-free [] l2 f1 f2 = f2
    ∨-free (h1 ∷ t1) [] f1 f2 = f1
    ∨-free (h1 ∷ t1) (h2 ∷ t2) f1@(∷-Free h1 t1 min1 incomp1 ft1) f2@(∷-Free h2 t2 min2 incomp2 ft2) with keep (h1 ∦? h2)
    ... | yes (inj₁ h1⊑h2) , q rewrite q = ∨-free t1 (h2 ∷ t2) ft1 f2 
    ... | yes (inj₂ h2⊑h1) , q rewrite q = ∨-free (h1 ∷ t1) t2 f1 ft2
    ... | no ¬h1∦h2 , q with keep (h1 <? h2)
    ... | yes h1<h2 , r rewrite q | r = {!!}
      where
        transitive : Transitive _<_
        transitive = IsStrictTotalOrder.trans isStrictTotalOrder 

        h1<t2 : All (h1 <_) t2
        h1<t2 = LA.map {P = h2 <_} {Q = h1 <_} (λ {x} → λ h2<x → transitive h1<h2 h2<x) min2

        min : All (h1 <_) (∨ t1 (h2 ∷ t2))
        min = ∨-All t1 (h2 ∷ t2) min1 (h1<h2 ∷ h1<t2)  

        incomp : ¬ (Any (λ x → (h1 ⊑ x) ⊎ (x ⊑ h1)) (∨ t1 (h2 ∷ t2)))
        incomp p = {!!} --unimodality is necessary here

    ... | no ¬h1<h2 , r rewrite q | r = {!!} 


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

    



    
