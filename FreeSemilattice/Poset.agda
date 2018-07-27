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

module FreeSemilattice.Poset (P : DeltaPoset0) where

open import FreeSemilattice P
open DeltaPoset0 P

infix 4 _≈_

_≈_ : Rel Carrier-FP l0
(l1 , f1) ≈ (l2 , f2) = l1 ≡ l2

≈-refl : Reflexive _≈_
≈-refl {s} = PE.refl

≈-sym : Symmetric _≈_
≈-sym {l1 , f1} {l2 , f2} PE.refl = PE.refl 

≈-trans : Transitive _≈_
≈-trans {l1 , f1} {l2 , f2} {l3 , f3} PE.refl PE.refl = PE.refl

≈-isEquiv : IsEquivalence _≈_
≈-isEquiv = record 
  {
  refl = λ {s} → ≈-refl {s} ; 
  sym = λ {s1} → λ {s2} → ≈-sym {s1} {s2} ;
  trans = λ {s1} → λ {s2} → λ {s3} → ≈-trans {s1} {s2} {s3} 
  }

≤-resp-≈ʳ : {s1 s2 s3 : Carrier-FP} → (s2 ≈ s3) → s1 ≤ s2 → s1 ≤ s3
≤-resp-≈ʳ {.([] , []-Free)} {.(proj₁ s3) , snd} {s3} PE.refl []-≤ = []-≤
≤-resp-≈ʳ {(h1 ∷ t1 , f1)} {.(h3 ∷ t3) , f2} {(h3 ∷ t3) , f3} PE.refl (cmp-≤ ft1 f1 f2 h1⊑h2 t1≤l2) = cmp-≤ ft1 f1 f3 h1⊑h2 (≤-resp-≈ʳ PE.refl t1≤l2) 
≤-resp-≈ʳ {(h1 ∷ t1 , f1)} {.(h3 ∷ t3) , f2} {(h3 ∷ t3) , f3} PE.refl (skip-≤ f1 ft2 f2 h2<h1 h1∥h2 l1≤t2) = skip-≤ f1 ft2 f3 h2<h1 h1∥h2 (≤-resp-≈ʳ PE.refl l1≤t2)


mutual
 t≤h∷t : {h : Carrier} → {t : List Carrier} → (f : IsFreeList _<_ _⊑_ (h ∷ t)) → (ft : IsFreeList _<_ _⊑_ t) → 
          (t , ft) ≤ (h ∷ t , f)
 t≤h∷t {h} {[]} f []-Free = []-≤
 t≤h∷t {h} {t@(h' ∷ t')} f@(∷-Free .h .t min incomp _) ft = skip-≤ ft ft f h<h' (∥-sym h∥h') (≤-refl-lemma t ft ft)   
   where
     h<h' : h < h'
     h<h' = head min

     h∥h' : h ∥ h'
     h∥h' h∦h' = incomp $ here (h∦h') 

 ≤-refl-lemma : (x : List Carrier) → (f1 f2 : IsFreeList _<_ _⊑_ x) → (x , f1) ≤ (x , f2)
 ≤-refl-lemma []  []-Free []-Free = []-≤
 ≤-refl-lemma (h ∷ t) f@(∷-Free .h .t min incomp ft) f'@(∷-Free .h .t min' incomp' ft')  = 
   cmp-≤ ft f f' (reflexive PE.refl) (t≤h∷t f' ft) 

≤-refl : {x y : Carrier-FP} → x ≈ y → x ≤ y
≤-refl {l , f} {.l , f'} PE.refl = ≤-refl-lemma l f f'

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

≤-irrel : {l1 l2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ l1} → {f1' : IsFreeList _<_ _⊑_ l1} → 
          {f2 : IsFreeList _<_ _⊑_ l2} → 
          {f2' : IsFreeList _<_ _⊑_ l2} → (l1 , f1) ≤ (l2 , f2) → (l1 , f1') ≤ (l2 , f2')
≤-irrel l1≤l2 = ≤-irrelˡ (≤-irrelʳ l1≤l2)


≤-push : (h2 : Carrier) → {l1 t2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ l1} → {ft2 : IsFreeList _<_ _⊑_ t2} → {f2 : IsFreeList _<_ _⊑_ (h2 ∷ t2)} → 
         (l1 , f1) ≤ (t2 , ft2) → (l1 , f1) ≤ ((h2 ∷ t2) , f2)
≤-push h2 {.[]} {t2} {.[]-Free} {ft2} {f2} []-≤ = []-≤
≤-push h2 {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2} l1≤t2@(cmp-≤ ft1 .f1 ft2' h1⊑th2 t1≤t2) with t1≤l2 | h1 ∦? h2 
  where 
    t1≤l2 : (t1 , ft1) ≤ (h2 ∷ t2h ∷ t2t , f2)
    t1≤l2 = ≤-push h2 t1≤t2
≤-push h2 {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2} (cmp-≤ ft1 .f1 ft2' h1⊑t2h t1≤t2) | t1≤l2 | l⊑r h1⊑h2 _ = cmp-≤ ft1 f1 f2 h1⊑h2 t1≤l2
≤-push h2 {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2@(∷-Free .h2 t2 _ incomp2 _)} (cmp-≤ ft1 .f1 _ h1⊑t2h t1≤t2) | t1≤l2 | r⊑l _ h2⊑h1 = ⊥-elim $ incomp2 (here (inj₁ (transitive⊑ h2⊑h1 h1⊑t2h)))
≤-push h2 {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2} (cmp-≤ ft1 .f1 ft2' h1⊑t2h t1≤t2) | t1≤l2 | l≡r h1≡h2 = cmp-≤ ft1 f1 f2 (reflexive h1≡h2) t1≤l2
≤-push h2 {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2@(∷-Free .h2 t2 min2 _ _)} l1≤t2@(cmp-≤ ft1 .f1 ft2' h1⊑t2h t1≤t2) | t1≤l2 | l∥r h1∥h2 with compare h1 h2
... | tri< h1<h2 _ _ = ⊥-elim $ (unimodality h1<h2 (head min2) (∦-refl h1) h1∥h2) (inj₁ h1⊑t2h)
... | tri≈ _ h1≡h2 _ = ⊥-elim $ h1∥h2 (inj₁ (reflexive h1≡h2))
... | tri> _ _ h2<h1 = skip-≤ f1 ft2 f2 h2<h1 h1∥h2 l1≤t2 
≤-push h2 {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2} (skip-≤ .f1 ft2' _ t2h<h1 h1∥t2h l1≤t2) with compare h1 h2
≤-push h2 {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2@(∷-Free _ _ min2 _ _)} (skip-≤ .f1 ft2' _ t2h<h1 h1∥t2h l1≤t2t) | tri< h1<h2 _ _ = 
  ⊥-elim $ irrefl PE.refl $ (transitive< (transitive< h1<h2 (head min2)) t2h<h1) 
≤-push .h1 {h1 ∷ t1} {t2h ∷ t2t} {f1} {ft2} {f2@(∷-Free _ _ min2 _ _)} (skip-≤ .f1 ft2' _ t2h<h1 h1∥t2h l1≤t2t) | tri≈ _ h1≡h2@PE.refl _ =
  ⊥-elim $ irrefl PE.refl $ (transitive< t2h<h1 (head min2))
≤-push h2 {h1 ∷ t1} {t2@(t2h ∷ t2t)} {f1} {ft2} {f2@(∷-Free _ _ min2 incomp2 _)} l1≤t2@(skip-≤ .f1 ft2' _ t2h<h1 h1∥t2h l1≤t2t) | tri> _ _ h2<h1 = 
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
    q = ≤-push h2 p

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

≤-antisym-lemma : {l1 l2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ l1} → {f2 : IsFreeList _<_ _⊑_ l2} → (l1 , f1) ≤ (l2 , f2) → (l2 , f2) ≤ (l1 , f1) → l1 ≡ l2
≤-antisym-lemma {.[]} {[]} {.[]-Free} {f2} []-≤ _ = PE.refl
≤-antisym-lemma {.[]} {h2 ∷ l2} {.[]-Free} {f2} []-≤ ()
≤-antisym-lemma {h1 ∷ t1} {h2 ∷ t2} {f1} {f2} l1≤l2@(cmp-≤ ft1 _ _ h1⊑h2 t1≤l2) l2≤l1@(cmp-≤ ft2 _ _ h2⊑h1 t2≤l1) with h1≡h2
  where
    h1≡h2 : h1 ≡ h2
    h1≡h2 = antisym h1⊑h2 h2⊑h1
≤-antisym-lemma{h1 ∷ t1} {.h1 ∷ t2} {f1@(∷-Free .h1 .t1 min1 incomp1 _)} {f2@(∷-Free .h1 .t2 min2 incomp2 _)} (cmp-≤ ft1 _ _ _ t1≤l2) (cmp-≤ ft2 _ _ h1⊑h1 t2≤l1) | PE.refl with (≤-antisym-lemma t1≤t2 t2≤t1) 
  where
    t1≤t2 : (t1 , ft1) ≤ (t2 , ft2)
    t1≤t2 = ≤-incomp-lemma incomp1 incomp2 t1≤l2

    t2≤t1 : (t2 , ft2) ≤ (t1 , ft1)
    t2≤t1 = ≤-incomp-lemma incomp2 incomp1 t2≤l1
≤-antisym-lemma {h1 ∷ t1} {.h1 ∷ t2} {f1@(∷-Free .h1 .t1 min1 incomp1 _)} {f2@(∷-Free .h1 .t2 min2 incomp2 _)} (cmp-≤ ft1 _ _ _ t1≤l2) (cmp-≤ ft2 _ _ h1⊑h1 t2≤l1) | PE.refl | PE.refl = PE.refl
≤-antisym-lemma {h1 ∷ t1} {h2 ∷ t2} {f1@(∷-Free .h1 .t1 min1 incomp1 _)} {f2@(∷-Free .h2 .t2 min2 incomp2 _)} (skip-≤ f1 _ f2 h2<h1 h1∥h2 l1≤t2) (cmp-≤ ft2 _ _ h1⊑h1 t2≤l1) with (≤-antisym-lemma l1≤t2 (≤-irrelˡ t2≤l1))
≤-antisym-lemma {h1 ∷ t1} {h2 ∷ t2} {f1@(∷-Free .h1 .t1 min1 incomp1 _)} {f2@(∷-Free .h2 .t2 min2 incomp2 _)} (skip-≤ f1 _ _ h2<h1 h1∥h2 l1≤t2) (cmp-≤ ft2 _ _ h2⊑h1 t2≤l1) | PE.refl = ⊥-elim $ incomp2 (here (inj₁ h2⊑h1)) 
≤-antisym-lemma {h1 ∷ t1} {h2 ∷ t2} {f1@(∷-Free .h1 .t1 min1 incomp1 _)} {f2@(∷-Free .h2 .t2 min2 incomp2 _)} (cmp-≤ _ _ _ h1⊑h2 t1≤l2) (skip-≤ _ _ _ h1<h2 h2∥h1 l2≤t1) with (≤-antisym-lemma l2≤t1 (≤-irrelˡ t1≤l2))
≤-antisym-lemma {h1 ∷ t1} {h2 ∷ t2} {f1@(∷-Free .h1 .t1 min1 incomp1 _)} {f2@(∷-Free .h2 .t2 min2 incomp2 _)} (cmp-≤ _ _ _ h1⊑h2 t1≤l2) (skip-≤ _ _ _ h1<h2 h2∥h1 l2≤t1) | PE.refl = ⊥-elim $ incomp1 (here (inj₁ h1⊑h2)) 
≤-antisym-lemma {h1 ∷ t1} {h2 ∷ t2} {f1@(∷-Free .h1 .t1 min1 incomp1 _)} {f2@(∷-Free .h2 .t2 min2 incomp2 _)} (skip-≤ _ _ _ h2<h1 h1∥h2 l1≤t2) (skip-≤ _ _ _ h1<h2 h2∥h1 l2≤t1) = ⊥-elim $ irrefl PE.refl $ (transitive< h1<h2 h2<h1)

≤-antisym : {s1 s2 : Carrier-FP} → (s1 ≤ s2) → (s2 ≤ s1) → s1 ≈ s2
≤-antisym {l1 , f1} {l2 , f2} s1≤s2 s2≤s1 = ≤-antisym-lemma s1≤s2 s2≤s1 


≤-cong : (h : Carrier) → {l1 l2 : List Carrier} → {f1 : IsFreeList _<_ _⊑_ l1} → {f2 : IsFreeList _<_ _⊑_ l2} →
         (f1' : IsFreeList _<_ _⊑_ (h ∷ l1)) → (f2' : IsFreeList _<_ _⊑_ (h ∷ l2)) → (l1 , f1) ≤ (l2 , f2) → 
         (h ∷ l1 , f1') ≤ (h ∷ l2 , f2')

≤-cong h {l1} {l2} {f1} {f2} f1' f2' l1≤l2 = cmp-≤ f1 f1' f2' (reflexive PE.refl) (≤-push h l1≤l2)

FP-Poset0 : Poset l1 l0 l1
FP-Poset0 = record 
    {
    Carrier = Carrier-FP ; 
    _≈_ = _≈_ ;
    _≤_ = _≤_ ;
    isPartialOrder = record 
        {
        isPreorder = record 
            {
            isEquivalence = ≈-isEquiv ;
            reflexive = ≤-refl ;
            trans = ≤-trans
            } ;
        antisym = ≤-antisym
        }
    }
