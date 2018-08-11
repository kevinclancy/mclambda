open import Function using (_$_)
open import Function.Equivalence as FE
open import Function.Equality using (_⟨$⟩_)
open import Data.Empty
open import Data.List
open import Data.List.All as LA
open import Data.List.Any as LAny
open import Data.List.Any.Properties as LAP
import Data.List.Relation.Pointwise as PW
open import Data.List.Relation.Pointwise using (_∷_ ; [])
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE
open import RelationalStructures
open import Util

module FreeSemilattice.Poset {c ℓ⊑ ℓ< ℓ~} (P : DeltaPoset {c} {ℓ⊑} {ℓ<} {ℓ~}) where

open import FreeSemilattice.Core P
open DeltaPoset P renaming (_≈_ to _~_ ; trans≈ to trans~ ; sym≈ to sym~ ; refl≈ to refl~ ;
  ∦-respʳ-≈ to ∦-respʳ-~ ; ∦-respˡ-≈ to ∦-respˡ-~ ;
  ∥-respʳ-≈ to ∥-respʳ-~ ; ∥-respˡ-≈ to ∥-respˡ-~ ;
  <-respʳ-≈ to <-respʳ-~ ; <-respˡ-≈ to <-respˡ-~ ; 
  ⊑-respʳ-≈ to ⊑-respʳ-~ ; ⊑-respˡ-≈ to ⊑-respˡ-~ ;
  ≈-decSetoid to ~-decSetoid ; _≈?_ to _~?_)

open import Data.List.Membership.DecSetoid ~-decSetoid
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)

infix 4 _≈_

⋜-resp-≈ʳ : {s1 s2 s3 : Carrier-FP} → (s2 ≈ s3) → s1 ⋜ s2 → s1 ⋜ s3
⋜-resp-≈ʳ {.([] , []-Free)} {l2 , snd} {s3} s2≈s3 []-⋜ = []-⋜
⋜-resp-≈ʳ {(h1 ∷ t1 , f1)} {h2 ∷ t2 , f2} {(h3 ∷ t3) , f3} (h2~h3 ∷ t2≈t3) (cmp-⋜ ft1 f1 f2 h1⊑h2 t1⋜l2) = 
  cmp-⋜ ft1 f1 f3 (⊑-respʳ-~ h2~h3 h1⊑h2) (⋜-resp-≈ʳ (h2~h3 ∷ t2≈t3) t1⋜l2) 
⋜-resp-≈ʳ {(h1 ∷ t1 , f1)} {h2 ∷ t2 , f2} {(h3 ∷ t3) , f3@(∷-Free _ _ _ _ ft3)} (h2~h3 ∷ t2≈t3) (skip-⋜ f1 ft2 f2 h2<h1 h1∥h2 l1⋜t2) = 
  skip-⋜ f1 ft3 f3 (<-respˡ-~ h2~h3 h2<h1) (∥-respʳ-~ h2~h3 h1∥h2) (⋜-resp-≈ʳ t2≈t3 l1⋜t2)

mutual
 t⋜h∷t : {h : Carrier} → {t : List Carrier} → (f : IsFreeList (h ∷ t)) → (ft : IsFreeList t) → 
          (t , ft) ⋜ (h ∷ t , f)
 t⋜h∷t {h} {[]} f []-Free = []-⋜
 t⋜h∷t {h} {t@(h' ∷ t')} f@(∷-Free .h .t min incomp _) ft = skip-⋜ ft ft f h<h' (∥-sym h∥h') (⋜-refl-lemma t ft ft)   
   where
     h<h' : h < h'
     h<h' = head min

     h∥h' : h ∥ h'
     h∥h' h∦h' = incomp $ here (h∦h') 

 ⋜-refl-lemma : (x : List Carrier) → (f1 f2 : IsFreeList x) → (x , f1) ⋜ (x , f2)
 ⋜-refl-lemma []  []-Free []-Free = []-⋜
 ⋜-refl-lemma (h ∷ t) f@(∷-Free .h .t min incomp ft) f'@(∷-Free .h .t min' incomp' ft')  = 
   cmp-⋜ ft f f' (reflexive refl~) (t⋜h∷t f' ft) 

⋜-irrelˡ : {l1 l2 : List Carrier} → {f1 : IsFreeList l1} → {f1' : IsFreeList l1} → 
          {f2 : IsFreeList l2} → (l1 , f1) ⋜ (l2 , f2) → (l1 , f1') ⋜ (l2 , f2)
⋜-irrelˡ {.[]} {l2} {[]-Free} {[]-Free} {f2} l1⋜l2 = []-⋜ 
⋜-irrelˡ {h1 ∷ t1} {h2 ∷ t2} {∷-Free .h1 .t1 min1 incomp1 ft1} {f1'} {f2} (cmp-⋜ ft1' .(∷-Free h1 t1 min1 incomp1 ft1) .f2 h1⊑h2 l1⋜l2) = 
  cmp-⋜ ft1' f1' f2 h1⊑h2 l1⋜l2
⋜-irrelˡ {h1 ∷ t1} {h2 ∷ t2} {f1@(∷-Free .h1 .t1 _ _ _)} {f1'} {f2} (skip-⋜ .f1 ft2 .f2 h2<h1 h1∥h2 l1⋜t2) =
  skip-⋜ f1' ft2 f2 h2<h1 h1∥h2 (⋜-irrelˡ l1⋜t2) 

⋜-irrelʳ : {l1 l2 : List Carrier} → {f1 : IsFreeList l1} → {f2 : IsFreeList l2} → 
          {f2' : IsFreeList l2} → (l1 , f1) ⋜ (l2 , f2) → (l1 , f1) ⋜ (l2 , f2')

⋜-irrelʳ {.[]} {l2} {.[]-Free} {f2} {f2'} []-⋜ = []-⋜
⋜-irrelʳ {h1 ∷ t1} {h2 ∷ t2} {f1} {f2} {f2'} (cmp-⋜ ft1 .f1 .f2 h1⊑h2 t1⋜l2) = cmp-⋜ ft1 f1 f2' h1⊑h2 (⋜-irrelʳ t1⋜l2)
⋜-irrelʳ {h1 ∷ t1} {h2 ∷ t2} {f1} {f2} {f2'} (skip-⋜ .f1 ft2 .f2 h2<h1 h1∥h2 l1⋜t2) = skip-⋜ f1 ft2 f2' h2<h1 h1∥h2 l1⋜t2

⋜-irrel : {l1 l2 : List Carrier} → {f1 : IsFreeList l1} → {f1' : IsFreeList l1} → 
          {f2 : IsFreeList l2} → 
          {f2' : IsFreeList l2} → (l1 , f1) ⋜ (l2 , f2) → (l1 , f1') ⋜ (l2 , f2')
⋜-irrel l1⋜l2 = ⋜-irrelˡ (⋜-irrelʳ l1⋜l2)

⋜-refl : {x y : Carrier-FP} → x ≈ y → x ⋜ y
⋜-refl {.[] , f1} {.[] , f2} [] =  ⋜-irrelˡ $ []-⋜
⋜-refl {l1@(h1 ∷ t1) , f1@(∷-Free _ _ _ _ ft1)} {l2@(h2 ∷ t2) , f2@(∷-Free _ _ _ _ ft2)} (h1~h2 ∷ t1≈t2) = 
  E-l1l2.from ⟨$⟩ l1≤l2
  where
    module E-t1t2 = Equivalence (⋜⇔≤ {t1 , ft1} {t2 , ft2})
    module E-l1l2 = Equivalence (⋜⇔≤ {l1 , f1} {l2 , f2})

    t1≤t2 : (t1 , ft1) ≤ (t2 , ft2)
    t1≤t2 = E-t1t2.to ⟨$⟩ (⋜-refl {t1 , ft1} {t2 , ft2} t1≈t2) 

    l1≤l2 : (h1 ∷ t1 , f1) ≤ (h2 ∷ t2 , f2) 
    l1≤l2 = (here $ reflexive h1~h2) ∷ (LA.map there t1≤t2)
 
sng-free : {c : Carrier} → (IsFreeList (c ∷ []))
sng-free {c} = ∷-Free c [] [] (λ ()) []-Free

≤-refl : {x y : Carrier-FP} → x ≈ y → x ≤ y
≤-refl {x} {y} x≈y = to ⟨$⟩ ⋜-refl x≈y  
  where
    open Equivalence (⋜⇔≤ {x} {y})

≤-trans : {s1 s2 s3 : Carrier-FP} → s1 ≤ s2 → s2 ≤ s3 → s1 ≤ s3
≤-trans {l1 , f1} {l2 , f2} {l3 , f3} s1≤s2 s2≤s3 = 
  LA.tabulate tab
  where
    tab : {x : Carrier} → x ∈≡ l1 → Any (x ⊑_) l3
    tab {x} x∈≡l1 = anyEliminate l2 elim (LA.lookup s1≤s2 x∈≡l1)
      where
        elim : AnyEliminator {ℓQ = l0} Carrier (Any (x ⊑_) l3) (x ⊑_) l2
        elim a f x⊑a a∈≡l2 = LAny.map (λ a⊑· → trans⊑ x⊑a a⊑·) (LA.lookup s2≤s3 a∈≡l2)

≤-antisym : {s1 s2 : Carrier-FP} → (s1 ≤ s2) → (s2 ≤ s1) → s1 ≈ s2
≤-antisym {[] , f1} {[] , f2} s1≤s2 s2≤s1 = 
  []
≤-antisym {[] , f1} {h2 ∷ t2 , f2} s1≤s2 s2≤s1 = 
  ⊥-elim $ ¬Any[] (LA.head s2≤s1)
≤-antisym {h1 ∷ t1 , f1} {[] , f2} s1≤s2 s2≤s1 = 
  ⊥-elim $ ¬Any[] (LA.head s1≤s2)
≤-antisym {l1@(h1 ∷ t1) , f1@(∷-Free _ _ min1 incomp1 ft1)} {l2@(h2 ∷ t2) , f2@(∷-Free _ _ min2 incomp2 ft2)} (h1⊑l2 ∷ t1≤l2) (h2⊑l1 ∷ t2≤l1) = 
  let 
    t1≈t2 : (t1 , ft1) ≈ (t2 , ft2)
    t1≈t2 = ≤-antisym {t1 , ft1} {t2 , ft2} t1≤t2 t2≤t1
  in
  h1~h2 ∷ t1≈t2
  where
    elim : AnyEliminator {ℓQ = l0} Carrier (h1 ~ h2) (h1 ⊑_) l2
    elim a f h1⊑a (here a≡h2@PE.refl) = anyEliminate l1 elim' h2⊑l1
      where
        elim' : AnyEliminator {ℓQ = ℓ⊑} Carrier (h1 ~ h2) (h2 ⊑_) l1
        elim' x f h2⊑x (here x≡h1@PE.refl) = 
          let
            h2~h1 : h2 ~ h1
            h2~h1 = antisym (trans⊑ h2⊑x (reflexive refl~)) h1⊑a  
          in
          sym~ h2~h1
        elim' x f h2⊑x (there x∈≡t1) = 
          let
            h1⊑x : h1 ⊑ x 
            h1⊑x = trans⊑ h1⊑a h2⊑x
          in
          ⊥-elim $ incomp1 $ LAny.map (λ x~· → inj₁ $ trans⊑ h1⊑x $ reflexive x~·) (a∈≡l→a∈l x∈≡t1)  
    elim a f h1⊑a (there a∈≡t2) with a⊑l1
      where
        a⊑l1 : Any (a ⊑_) l1
        a⊑l1 = LA.lookup t2≤l1 a∈≡t2  
    elim a f h1⊑a (there a∈≡t2) | here a⊑h1 =
      ⊥-elim $ anyEliminate l1 elim' h2⊑l1
      where
        a~h1 : a ~ h1
        a~h1 = antisym a⊑h1 h1⊑a

        h2<h1 : h2 < h1
        h2<h1 = <-respʳ-~ a~h1 (LA.lookup min2 a∈≡t2)
        
        h2∥h1 : h2 ∥ h1
        h2∥h1 h2∦h1 = incomp2 $ LAny.map (λ a~· → (∦-respʳ-~ (trans~ (sym~ a~h1) a~·) h2∦h1)) (a∈≡l→a∈l a∈≡t2)

        elim' : AnyEliminator {ℓQ = l0} Carrier ⊥ (h2 ⊑_) l1
        elim' x f h2⊑x (here x≡h1@PE.refl) = 
          h2∥h1 $ inj₁ (trans⊑ h2⊑x $ reflexive refl~) 
        elim' x f h2⊑x (there x∈≡t1) = 
          (unimodality h2<h1 (LA.lookup min1 x∈≡t1) (inj₁ $ reflexive refl~) h2∥h1) (inj₁ h2⊑x) 
    elim a f h1⊑a (there a∈≡t2) | there a⊑t1 =
      ⊥-elim $ incomp1 $ LAny.map (λ a⊑· → inj₁ $ trans⊑ h1⊑a a⊑·) a⊑t1

    h1~h2 : h1 ~ h2
    h1~h2 = anyEliminate l2 elim h1⊑l2

    t1≤t2 : (t1 , ft1) ≤ (t2 , ft2)
    t1≤t2 = LA.tabulate tab
      where
        tab : {x : Carrier} → x ∈≡ t1 → Any (x ⊑_) t2
        tab {x} x∈≡t1 with (LA.lookup t1≤l2 x∈≡t1) 
        tab {x} x∈≡t1 | here x⊑h2 = 
          let 
            x⊑h1 = ⊑-respʳ-~ (sym~ h1~h2) x⊑h2
          in
          ⊥-elim $ incomp1 $ LAny.map (λ x~· → inj₂ $ ⊑-respˡ-~ x~· x⊑h1) (a∈≡l→a∈l x∈≡t1) 
        tab {x} x∈≡t1 | there x⊑t2 = x⊑t2

    t2≤t1 : (t2 , ft2) ≤ (t1 , ft1)
    t2≤t1 = LA.tabulate tab
      where
        tab : {x : Carrier} → x ∈≡ t2 → Any (x ⊑_) t1
        tab {x} x∈≡t2 with (LA.lookup t2≤l1 x∈≡t2) 
        tab {x} x∈≡t2 | here x⊑h1 = 
          let 
            x⊑h2 = ⊑-respʳ-~ h1~h2 x⊑h1
          in
          ⊥-elim $ incomp2 $ LAny.map (λ x~· → inj₂ $ ⊑-respˡ-~ x~· x⊑h2) (a∈≡l→a∈l x∈≡t2) 
        tab {x} x∈≡t2 | there x⊑t1 = x⊑t1

FP-Poset : Poset _ _ _
FP-Poset = record 
    {
    Carrier = Carrier-FP ; 
    _≈_ = _≈_ ;
    _≤_ = _≤_ ;
    isPartialOrder = record 
        {
        isPreorder = record 
            {
            isEquivalence = ≈-isEquiv ;
            reflexive = λ {s1} → λ {s2} → ≤-refl {s1} {s2} ;
            trans = λ {s1} → λ {s2} → λ {s3} → ≤-trans {s1} {s2} {s3}
            } ;
        antisym = λ {s1} → λ {s2} → ≤-antisym {s1} {s2}
        }
    }
