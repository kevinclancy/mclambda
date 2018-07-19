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
    
    infix  4 _≈_ _≤_
    infixr 6 _∨'_
    infixr 6 _∨_

    _≈_ : Rel Carrier-FP l0
    (l1 , f1) ≈ (l2 , f2) = l1 ≡ l2

    data _≤_ : Carrier-FP → Carrier-FP → Set₁ where
      []-≤ : {cfp : Carrier-FP} → ([] , []-Free) ≤ cfp  
      cmp-≤ : {c d : Carrier} {c' d' : List Carrier} → (c'-free : IsFreeList _<_ _⊑_ c') →
              (cc'-free : IsFreeList _<_ _⊑_ (c ∷ c')) →
              (dd'-free : IsFreeList _<_ _⊑_ (d ∷ d')) →
              c ⊑ d →
              (c' , c'-free) ≤ (d ∷ d' , dd'-free) →
              (c ∷ c' , cc'-free) ≤ (d ∷ d' , dd'-free)
      skip-≤ : {c d : Carrier} {c' d' : List Carrier} → 
               (cc'-free : IsFreeList _<_ _⊑_ (c ∷ c')) → 
               (d'-free : IsFreeList _<_ _⊑_ d') → 
               (dd'-free : IsFreeList _<_ _⊑_ (d ∷ d')) →
               (d < c) → (c ∥ d) → (c ∷ c' , cc'-free) ≤ (d' , d'-free) →
               (c ∷ c' , cc'-free) ≤ (d ∷ d' , dd'-free)

    mutual
     t≤h∷t : {h : Carrier} → {t : List Carrier} → (f : IsFreeList _<_ _⊑_ (h ∷ t)) → (ft : IsFreeList _<_ _⊑_ t) → 
              (t , ft) ≤ (h ∷ t , f)
     t≤h∷t {h} {[]} f []-Free = []-≤
     t≤h∷t {h} {t@(h' ∷ t')} f@(∷-Free .h .t min incomp _) ft = skip-≤ ft ft f h<h' (∥-sym h∥h') (≤-refl-lemma t ft)   
       where
         h<h' : h < h'
         h<h' = head min

         h∥h' : h ∥ h'
         h∥h' h∦h' = incomp $ here (h∦h') 

     ≤-refl-lemma : (x : List Carrier) → (f : IsFreeList _<_ _⊑_ x) → (x , f) ≤ (x , f)
     ≤-refl-lemma []  []-Free = []-≤
     ≤-refl-lemma (h ∷ t) f@(∷-Free .h .t min incomp ft) = 
       cmp-≤ ft f f (reflexive PE.refl) (t≤h∷t f ft) 

    ≤-refl : (x : Carrier-FP) → x ≤ x
    ≤-refl (l , f) = ≤-refl-lemma l f  

    sng-free : {c : Carrier} → (IsFreeList _<_ _⊑_ (c ∷ []))
    sng-free {c} = ∷-Free c [] [] (λ ()) []-Free

    ≤-irrelˡ : {l1 l2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ l1} → {f1' : IsFreeList _<_ _⊑_ l1} → 
              {f2 : IsFreeList _<_ _⊑_ l2} → (l1 , f1) ≤ (l2 , f2) → (l1 , f1') ≤ (l2 , f2)
    ≤-irrelˡ {.[]} {l2} {[]-Free} {[]-Free} {f2} l1≤l2 = []-≤ 
    ≤-irrelˡ {h1 ∷ t1} {h2 ∷ t2} {∷-Free .h1 .t1 min1 incomp1 ft1} {f1'} {f2} (cmp-≤ ft1' .(∷-Free h1 t1 min1 incomp1 ft1) .f2 h1⊑h2 l1≤l2) = 
      cmp-≤ ft1' f1' f2 h1⊑h2 l1≤l2
    ≤-irrelˡ {h1 ∷ t1} {h2 ∷ t2} {f1@(∷-Free .h1 .t1 _ _ _)} {f1'} {f2} (skip-≤ .f1 ft2 .f2 h2<h1 h1∥h2 l1≤t2) =
      skip-≤ f1' ft2 f2 h2<h1 h1∥h2 (≤-irrelˡ l1≤t2) 

    ≤-irrelʳ : {l1 l2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ l1} → {f2 : IsFreeList _<_ _⊑_ l2} → 
              {f2' : IsFreeList _<_ _⊑_ l2} → (l1 , f1) ≤ (l2 , f2) → (l1 , f1) ≤ (l2 , f2')

    ≤-irrelʳ {.[]} {l2} {.[]-Free} {f2} {f2'} []-≤ = []-≤
    ≤-irrelʳ {h1 ∷ t1} {h2 ∷ t2} {f1} {f2} {f2'} (cmp-≤ ft1 .f1 .f2 h1⊑h2 t1≤l2) = cmp-≤ ft1 f1 f2' h1⊑h2 (≤-irrelʳ t1≤l2)
    ≤-irrelʳ {h1 ∷ t1} {h2 ∷ t2} {f1} {f2} {f2'} (skip-≤ .f1 ft2 .f2 h2<h1 h1∥h2 l1≤t2) = skip-≤ f1 ft2 f2' h2<h1 h1∥h2 l1≤t2

    ≤-push : {h2 : Carrier} → {l1 t2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ l1} → {ft2 : IsFreeList _<_ _⊑_ t2} → {f2 : IsFreeList _<_ _⊑_ (h2 ∷ t2)} → 
             (l1 , f1) ≤ (t2 , ft2) → (l1 , f1) ≤ ((h2 ∷ t2) , f2)
    ≤-push {h2} {.[]} {t2} {.[]-Free} {ft2} {f2} []-≤ = []-≤
    ≤-push {h2} {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2} l1≤t2@(cmp-≤ ft1 .f1 ft2' h1⊑th2 t1≤t2) with t1≤l2 | h1 ∦? h2 
      where 
        t1≤l2 : (t1 , ft1) ≤ (h2 ∷ t2h ∷ t2t , f2)
        t1≤l2 = ≤-push t1≤t2
    ≤-push {h2} {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2} (cmp-≤ ft1 .f1 ft2' h1⊑t2h t1≤t2) | t1≤l2 | l⊑r h1⊑h2 _ = cmp-≤ ft1 f1 f2 h1⊑h2 t1≤l2
    ≤-push {h2} {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2@(∷-Free .h2 t2 _ incomp2 _)} (cmp-≤ ft1 .f1 _ h1⊑t2h t1≤t2) | t1≤l2 | r⊑l _ h2⊑h1 = ⊥-elim $ incomp2 (here (inj₁ (transitive⊑ h2⊑h1 h1⊑t2h)))
    ≤-push {h2} {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2} (cmp-≤ ft1 .f1 ft2' h1⊑t2h t1≤t2) | t1≤l2 | l≡r h1≡h2 = cmp-≤ ft1 f1 f2 (reflexive h1≡h2) t1≤l2
    ≤-push {h2} {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2@(∷-Free .h2 t2 min2 _ _)} l1≤t2@(cmp-≤ ft1 .f1 ft2' h1⊑t2h t1≤t2) | t1≤l2 | l∥r h1∥h2 with compare h1 h2
    ... | tri< h1<h2 _ _ = ⊥-elim $ (unimodality h1<h2 (head min2) (∦-refl h1) h1∥h2) (inj₁ h1⊑t2h)
    ... | tri≈ _ h1≡h2 _ = ⊥-elim $ h1∥h2 (inj₁ (reflexive h1≡h2))
    ... | tri> _ _ h2<h1 = skip-≤ f1 ft2 f2 h2<h1 h1∥h2 l1≤t2 
    ≤-push {h2} {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2} (skip-≤ .f1 ft2' _ t2h<h1 h1∥t2h l1≤t2) with compare h1 h2
    ≤-push {h2} {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2@(∷-Free _ _ min2 _ _)} (skip-≤ .f1 ft2' _ t2h<h1 h1∥t2h l1≤t2t) | tri< h1<h2 _ _ = 
      ⊥-elim $ irrefl PE.refl $ (transitive< (transitive< h1<h2 (head min2)) t2h<h1) 
    ≤-push {.h1} {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2@(∷-Free _ _ min2 _ _)} (skip-≤ .f1 ft2' _ t2h<h1 h1∥t2h l1≤t2t) | tri≈ _ h1≡h2@PE.refl _ =
      ⊥-elim $ irrefl PE.refl $ (transitive< t2h<h1 (head min2))
    ≤-push {h2} {h1 ∷ t1} {t2@(t2h ∷ t2t)} {f1} {ft2} {f2@(∷-Free _ _ min2 incomp2 _)} l1≤t2@(skip-≤ .f1 ft2' _ t2h<h1 h1∥t2h l1≤t2t) | tri> _ _ h2<h1 = 
      skip-≤ f1 ft2 f2 h2<h1 (∥-sym h2∥h1) l1≤t2 
      where
        h2∥th2 : h2 ∥ t2h
        h2∥th2 h2∦t2h = incomp2 (here h2∦t2h)

        h2∥h1 : h2 ∥ h1
        h2∥h1 h2∦h1 = (unimodality (head min2) t2h<h1 (∦-refl h2) h2∥th2) h2∦h1 
    ≤-peel : {h1 : Carrier} → {t1 l2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ (h1 ∷ t1)} → {ft1 : IsFreeList _<_ _⊑_ t1} → {f2 : IsFreeList _<_ _⊑_ l2} → 
             ((h1 ∷ t1) , f1) ≤ (l2 , f2) → (t1 , ft1) ≤ (l2 , f2)
    ≤-peel {h1} {t1} {h2 ∷ t2} {f1} {ft1} {f2} (cmp-≤ ft1' .f1 .f2 h1⊑h2 t1≤l2) = ≤-irrelˡ t1≤l2
    ≤-peel {h1} {t1} {h2 ∷ t2} {f1} {ft1} {f2} (skip-≤ .f1 ft2 .f2 h2<h1 h1∥h2 l1≤t2) = q
      where 
        p : (t1 , ft1) ≤ (t2 , ft2)
        p = ≤-peel l1≤t2
 
        q : (t1 , ft1) ≤ (h2 ∷ t2 , f2)
        q = ≤-push p
  

  
    ≤-discard : {h1 h2 : Carrier} → {t1 t2 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ (h1 ∷ t1)) →
                (ft1 : IsFreeList _<_ _⊑_ t1) → (f2 : IsFreeList _<_ _⊑_ (h2 ∷ t2)) → 
                (ft2 : IsFreeList _<_ _⊑_ t2) → (h1 ⊑ h2) → (t1 , ft1) ≤ ((h2 ∷ t2) , f2) →
                ((h1 ∷ t1) , f1) ≤ ((h2 ∷ t2) , f2)  
    ≤-discard {h1} {h2} {.[]} {t2} f1 .[]-Free f2 ft2 h1⊑h2 []-≤ = 
      cmp-≤ []-Free f1 f2 h1⊑h2 []-≤
    ≤-discard {h1} {h2} {t1h ∷ t1t} {t2} f1 ft1@(∷-Free .t1h .t1t min-t1 incomp-t1 ftt1) f2 ft2 h1⊑h2 (cmp-≤ ftt1' .ft1 .f2 t1h⊑h2 t1t≤h2t2) = 
      cmp-≤ ft1 f1 f2 h1⊑h2 (≤-discard ft1 ftt1 f2 ft2 t1h⊑h2 (≤-irrelˡ t1t≤h2t2))
    ≤-discard {h1} {h2} {t1h ∷ t1t} {t2} f1 ft1 f2 ft2 h1⊑h2 t1≤h2t2@(skip-≤ .ft1 ft2' .f2 h2<t1h t1h∥h2 t1≤t2) = 
      cmp-≤ ft1 f1 f2 h1⊑h2 t1≤h2t2

    ≤-discardʳ : {h1 h2 : Carrier} → {t1 t2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ (h1 ∷ t1)} →
                {f2 : IsFreeList _<_ _⊑_ (h2 ∷ t2)} → {ft2 : IsFreeList _<_ _⊑_ t2} →  
                (h2 < h1) → ((h1 ∷ t1) , f1) ≤ (t2 , ft2) →
                ((h1 ∷ t1) , f1) ≤ ((h2 ∷ t2) , f2)  
    ≤-discardʳ {h1} {h2} {t1} {t2h ∷ t2t} {.f1} {f2} {.ft2} h1⊑h2 (cmp-≤ ftt2 f1 ft2 h1⊑t2h t1≤t2) = {!!}
    ≤-discardʳ {h1} {h2} {t1} {.(_ ∷ _)} {.cc'-free} {f2} {.dd'-free} h1⊑h2 (skip-≤ cc'-free d'-free dd'-free x x₁ h1t1≤t2) = {!!}


    ≤-tran-lemma : {l1 l2 l3 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → 
             (f3 : IsFreeList _<_ _⊑_ l3) → ((l1 , f1) ≤ (l2 , f2)) → ((l2 , f2) ≤ (l3 , f3)) → ((l1 , f1) ≤ (l3 , f3))

    ≤-tran-lemma {.[]} {l2} {l3} f1 f2 f3 []-≤ l2≤l3 = []-≤ 
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {l3} f1@(∷-Free _ _ _ _ ft1) f2 f3 (cmp-≤ ft1' .f1 .f2 h1⊑h2 t1≤l2) l2≤l3 with t1≤l3 
      where
        t1≤l3 : (t1 , ft1) ≤ (l3 , f3)
        t1≤l3 = ≤-tran-lemma ft1 f2 f3 (≤-irrelˡ t1≤l2) l2≤l3 
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} f1@(∷-Free .h1 .t1 _ _ ft1) f2 f3@(∷-Free _ _ _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (cmp-≤ c'-free .f2 .(∷-Free _ _ _ _ ft3) h2⊑h3 t2≤l3) | t1≤l3 = 
      ≤-discard f1 ft1 f3 ft3 h1⊑h3 t1≤l3
      where
        h1⊑h3 : h1 ⊑ h3
        h1⊑h3 = transitive⊑ h1⊑h2 h2⊑h3
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} f1@(∷-Free _ _ _ _ ft1) f2 f3@(∷-Free _ _ _ _ ft3) l1≤l2@(cmp-≤ ft1' .(∷-Free _ _ _ _ ft1) .f2 h1⊑h2 t1≤l2) l2≤l3@(skip-≤ .f2 ft3' .(∷-Free _ _ _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 with compare h1 h3
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} (∷-Free .h1 .t1 _ _ ft1) f2 (∷-Free .h3 .t3 _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri< h1<h3 _ _ with h1 ∦? h3
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} f1@(∷-Free .h1 .t1 _ _ ft1) f2 f3@(∷-Free .h3 .t3 _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri< h1<h3 _ _ | l⊑r h1⊑h3 ¬h3⊑h1 = ≤-discard f1 ft1 f3 ft3 h1⊑h3 t1≤l3 
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} (∷-Free .h1 .t1 _ _ ft1) f2 (∷-Free .h3 .t3 _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri< h1<h3 _ _ | r⊑l ¬h1⊑h3 h3⊑h1 = ⊥-elim $ h2∥h3 (inj₂ (transitive⊑ h3⊑h1 h1⊑h2))
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} (∷-Free .h1 .t1 _ _ ft1) f2 (∷-Free .h3 .t3 _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri< h1<h3 _ _ | l≡r h1≡h3@PE.refl = ⊥-elim $ h2∥h3 (inj₂ h1⊑h2)
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} (∷-Free .h1 .t1 _ _ ft1) f2 (∷-Free .h3 .t3 _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri< h1<h3 _ _ | l∥r h1∥h3 = ⊥-elim $ (unimodality h1<h3 h3<h2 (inj₁ $ reflexive PE.refl) h1∥h3) (inj₁ h1⊑h2)

    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} (∷-Free .h1 .t1 _ _ ft1) f2 (∷-Free .h3 .t3 _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri≈ _ h1≡h3@PE.refl _ = 
      ⊥-elim $ h2∥h3 (inj₂ h1⊑h2)
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} (∷-Free .h1 .t1 _ _ ft1) f2 (∷-Free .h3 .t3 _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri> _ _ h3<h1 with h1 ∦? h3 
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} f1@(∷-Free .h1 .t1 _ _ ft1) f2 f3@(∷-Free .h3 .t3 _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri> _ _ h3<h1 | l⊑r h1⊑h3 ¬h3⊑h1 = ≤-discard f1 ft1 f3 ft3 h1⊑h3 t1≤l3
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} (∷-Free .h1 .t1 _ _ ft1) f2 (∷-Free .h3 .t3 _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri> _ _ h3<h1 | r⊑l ¬h1⊑h3 h3⊑h1 = ⊥-elim $ h2∥h3 (inj₂ (transitive⊑ h3⊑h1 h1⊑h2))
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} f1@(∷-Free .h1 .t1 _ _ ft1) f2 f3@(∷-Free .h3 .t3 _ _ ft3) (cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri> _ _ h3<h1 | l≡r h1≡h3 = ≤-discard f1 ft1 f3 ft3 (reflexive h1≡h3) t1≤l3
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {h3 ∷ t3} f1@(∷-Free .h1 .t1 _ _ ft1) f2 f3@(∷-Free .h3 .t3 _ _ ft3) l1≤l2@(cmp-≤ ft1' .(∷-Free h1 t1 _ _ ft1) .f2 h1⊑h2 t1≤l2) (skip-≤ .f2 ft3' .(∷-Free h3 t3 _ _ ft3) h3<h2 h2∥h3 l2≤t3) | t1≤l3 | tri> _ _ h3<h1 | l∥r h1∥h3 = skip-≤ f1 ft3 f3 h3<h1 h1∥h3 ((≤-tran-lemma f1 f2 ft3 l1≤l2 (≤-irrelʳ l2≤t3)))
    ≤-tran-lemma {h1 ∷ t1} {h2 ∷ t2} {l3} f1 f2 f3 (skip-≤ .f1 ft2 .f2 x x₁ l1≤l2) l2≤l3 =  ≤-irrelʳ $ ≤-tran-lemma f1 ft2 f3 l1≤l2 (≤-peel l2≤l3)

    ≤-trans : {s1 s2 s3 : Carrier-FP} → s1 ≤ s2 → s2 ≤ s3 → s1 ≤ s3
    ≤-trans {l1 , f1} {l2 , f2} {l3 , f3} s1≤s2 s2≤s3 = ≤-tran-lemma f1 f2 f3 s1≤s2 s2≤s3   

    ≤-incomp-lemma : {h : Carrier} → {t1 t2 : List Carrier} → {ft1 : IsFreeList _<_ _⊑_ t1} → {ft2 : IsFreeList _<_ _⊑_ t2} → {fht2 : IsFreeList _<_ _⊑_ (h ∷ t2)} → 
                     ¬ (Any (h ∦_) t1) → ¬ (Any (h ∦_) t2) → (t1 , ft1) ≤ (h ∷ t2 , fht2) → (t1 , ft1) ≤ (t2 , ft2)
    ≤-incomp-lemma {h} {.[]} {t2} {.[]-Free} {ft2} {fht2} incomp1 incomp2 []-≤ = []-≤ 
    ≤-incomp-lemma {h} {t1h ∷ t1t} {t2} {.ft1} {ft2} {.fht2} incomp1 incomp2 (cmp-≤ ft1t ft1 fht2 t1h⊑h t1≤h2t) = ⊥-elim $ incomp1 (here (inj₂ t1h⊑h))
    ≤-incomp-lemma {h} {t1h ∷ t1t} {t2} {.ft1} {ft2} {.fht2} incomp1 incomp2 (skip-≤ ft1 _ fht2 h<t1h t1h∥h t1≤h2t) = ≤-irrelʳ t1≤h2t

    ≤-antisym : {l1 l2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ l1} → {f2 : IsFreeList _<_ _⊑_ l2} → (l1 , f1) ≤ (l2 , f2) → (l2 , f2) ≤ (l1 , f1) → l1 ≡ l2
    ≤-antisym {.[]} {[]} {.[]-Free} {f2} []-≤ _ = PE.refl
    ≤-antisym {.[]} {h2 ∷ l2} {.[]-Free} {f2} []-≤ ()
    ≤-antisym {h1 ∷ t1} {h2 ∷ t2} {f1} {f2} l1≤l2@(cmp-≤ ft1 _ _ h1⊑h2 t1≤l2) l2≤l1@(cmp-≤ ft2 _ _ h2⊑h1 t2≤l1) with h1≡h2
      where
        h1≡h2 : h1 ≡ h2
        h1≡h2 = antisym h1⊑h2 h2⊑h1
    ≤-antisym {h1 ∷ t1} {.h1 ∷ t2} {f1@(∷-Free .h1 .t1 min1 incomp1 _)} {f2@(∷-Free .h1 .t2 min2 incomp2 _)} (cmp-≤ ft1 _ _ _ t1≤l2) (cmp-≤ ft2 _ _ h1⊑h1 t2≤l1) | PE.refl with (≤-antisym t1≤t2 t2≤t1) 
      where
        t1≤t2 : (t1 , ft1) ≤ (t2 , ft2)
        t1≤t2 = ≤-incomp-lemma incomp1 incomp2 t1≤l2
    
        t2≤t1 : (t2 , ft2) ≤ (t1 , ft1)
        t2≤t1 = ≤-incomp-lemma incomp2 incomp1 t2≤l1
    ≤-antisym {h1 ∷ t1} {.h1 ∷ t2} {f1@(∷-Free .h1 .t1 min1 incomp1 _)} {f2@(∷-Free .h1 .t2 min2 incomp2 _)} (cmp-≤ ft1 _ _ _ t1≤l2) (cmp-≤ ft2 _ _ h1⊑h1 t2≤l1) | PE.refl | PE.refl = PE.refl

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

    ∨'-idemʳ : {s : Carrier-FP} → (s ∨' ⊥' ≈ s)
    ∨'-idemʳ {l , f} = ∨-idem l

    ∨'-idemˡ : {s : Carrier-FP} → (⊥' ∨' s ≈ s) 
    ∨'-idemˡ {l , f} = ∨-idemˡ l

{-
    ∨'-sup1 : {l1 l2 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → 
               (l1 , f1) ≤ ((l1 , f1) ∨' (l2 , f2))
    ∨'-sup1 []  []-Free [] []-Free = []-≤
    ∨'-sup1 ([] , []-Free) (h ∷ t , f2) = []-≤ 
    ∨'-sup1 s@(h1 ∷ t1 , f1) ([] , []-Free) = ≤-refl {s} PE.refl
    ∨'-sup1 s1@(h1 ∷ t1 , f1) (h2 ∷ t2 , f2) with h1 ∦? h2 
    ... | p = {!!}
-}

    ∨'-sup : Supremum _≤_ _∨'_ 
    ∨'-sup ([] , []-Free) ([] , []-Free) = ([]-≤ , []-≤ , least)  
      where 
        least : ∀ z → (⊥' ≤ z) → (⊥' ≤ z) → ((⊥' ∨' ⊥') ≤ z)
        least z p q = []-≤ 
    ∨'-sup ([] , []-Free) s@(h2 ∷ t2 , f2) rewrite ∨'-idemˡ {s} =  ([]-≤ , ≤-refl s , least) 
      where 
        least : ∀ z → (p : ⊥' ≤ z) → (q : s ≤ z) → (s ≤ z)
        least z p q = q 
    ∨'-sup s@(h1 ∷ t1 , f1) ([] , []-Free) rewrite ∨'-idemʳ {s} = (≤-refl s , []-≤ , least)
      where 
        least : ∀ z → (p : s ≤ z) → (q : ⊥' ≤ z) → (s ≤ z)
        least z p q = p      
    ∨'-sup s1@(h1 ∷ t1 , f1@(∷-Free .h1 .t1 min1 incomp1 ft1) ) s2@(h2 ∷ t2 , f2@(∷-Free .h2 .t2 min2 incomp2 ft2)) with h1 ∦? h2
    ∨'-sup (h1 ∷ t1 , f1@(∷-Free .h1 .t1 min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-Free .h2 .t2 min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 = {!!}
      where  
        goal1 : (h1 ∷ t1 , f1) ≤ (h1 ∷ t1 , f1) ∨' (h2 ∷ t2 , f2)
        goal1 with h1 ∦? h2
        goal1 | l⊑r h1⊑h2 ¬h2⊑h1 with compare h1 h2
        goal1 | l⊑r h1⊑h2 ¬h2⊑h1 | tri< h1<h2 _ _ = {!skip!}
        goal1 | l⊑r h1⊑h2 ¬h2⊑h1 | tri≈ _ h1≡h2 _ = ⊥-elim $ ¬h2⊑h1 (reflexive (PE.sym h1≡h2))
        goal1 | l⊑r h1⊑h2 ¬h2⊑h1 | tri> _ _ h2<h1 = {!!}
         {- where
            t1≤t1∨h2t2 : (t1 , ft1) ≤ (t1 , ft1) ∨' (h2 ∷ t2 , f2)
            t1≤t1∨h2t2 with ∨'-sup (t1 , ft1) (h2 ∷ t2 , f2)
            t1≤t1∨h2t2 | (a , b , c) = a
        -}

        goal1 | DeltaPoset0.r⊑l x x₁ = {!!}
        goal1 | DeltaPoset0.l≡r x = {!!}
        goal1 | DeltaPoset0.l∥r x = {!!} 

    ∨'-sup (h1 ∷ t1 , ∷-Free .h1 .t1 min1 incomp1 ft1) (h2 ∷ t2 , ∷-Free .h2 .t2 min2 incomp2 ft2) | r⊑l x x₁ = {!!}
    ∨'-sup (h1 ∷ t1 , ∷-Free .h1 .t1 min1 incomp1 ft1) (h2 ∷ t2 , ∷-Free .h2 .t2 min2 incomp2 ft2) | DeltaPoset0.l≡r x = {!!}
    ∨'-sup (h1 ∷ t1 , ∷-Free .h1 .t1 min1 incomp1 ft1) (h2 ∷ t2 , ∷-Free .h2 .t2 min2 incomp2 ft2) | DeltaPoset0.l∥r x = {!!}
      

    
    
