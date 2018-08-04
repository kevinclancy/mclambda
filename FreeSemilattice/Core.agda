open import Function using (_$_)
open import Function.Equivalence as FE
open import Function.Equality using (_⟨$⟩_)
open import Data.Empty
open import Data.List
open import Data.List.Properties as LP
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

module FreeSemilattice.Core (P : DeltaPoset0) where

open DeltaPoset0 P renaming (trans to tran)


infix 4 _≈_ _⋜_ _≤_
infixr 6 _∨'_
infixr 6 _∨_

data IsFreeList {A : Set l0} (_<_ : Rel A l0) (_⊑_ : Rel A l0) : List A → Set l1 where
  []-Free : IsFreeList _<_ _⊑_ []
  ∷-Free : (hd : A) → (tl : List A) → (All (hd <_) tl) → ¬ (Any (λ x → (hd ⊑ x) ⊎ (x ⊑ hd)) tl) → 
            (IsFreeList _<_ _⊑_ tl) → IsFreeList _<_ _⊑_ (hd ∷ tl) 

free-incomp : {l : List Carrier} → (f : IsFreeList _<_ _⊑_ l) → {a b : Carrier} → a ∈ l → b ∈ l → a ∦ b → a ≡ b
free-incomp {[]} f {a} {b} a∈l b∈l a∦b = ⊥-elim $ ¬Any[] a∈l
free-incomp {h ∷ t} f {a} {b} (here a≡h) (here b≡h) a∦b = PE.trans a≡h (PE.sym b≡h) 
free-incomp {.a ∷ t} f@(∷-Free .a t min incomp ft) {a} {b} (here a≡h@PE.refl) (there b∈t) a∦b =
  ⊥-elim $ anyEliminate t eliminator b∈t 
  where
    eliminator : AnyEliminator Carrier ⊥ (b ≡_) t
    eliminator x f b≡x@PE.refl x∈t = incomp (f (a ∦_) a∦b)
free-incomp {.b ∷ t} f@(∷-Free .b t min incomp ft) {a} {b} (there a∈t) (here b≡h@PE.refl) a∦b =
  ⊥-elim $ anyEliminate t eliminator a∈t 
  where
    eliminator : AnyEliminator Carrier ⊥ (a ≡_) t
    eliminator x f a≡x@PE.refl x∈t = incomp (f (b ∦_) (∦-sym a∦b))
free-incomp {h ∷ t} f@(∷-Free h t min incomp ft) {a} {b} (there a∈t) (there b∈t) a∦b =
  free-incomp ft a∈t b∈t a∦b

free-eq : {l1 l2 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → 
          (∀ (a : Carrier) → a ∈ l1 ⇔ a ∈ l2) → l1 ≡ l2

free-eq {l1} {l2} f1 f2 a∈l1⇔a∈l2 with a∈l2→a∈l1 | a∈l1→a∈l2
  where
    a∈l2→a∈l1 : (a : Carrier) → a ∈ l2 → a ∈ l1
    a∈l2→a∈l1 a a∈l2 = from ⟨$⟩ a∈l2
      where
        open Equivalence (a∈l1⇔a∈l2 a)

    a∈l1→a∈l2 : (a : Carrier) → a ∈ l1 → a ∈ l2
    a∈l1→a∈l2 a a∈l1 = to ⟨$⟩ a∈l1
      where
        open Equivalence (a∈l1⇔a∈l2 a)
free-eq {[]} {[]} f1 f2 a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 = 
  PE.refl
free-eq {[]} {h2 ∷ t2} f1 f2 a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 = 
  ⊥-elim $ ¬Any[] (a∈l2→a∈l1 h2 $ here PE.refl)
free-eq {h1 ∷ t1} {[]} f1 f2 a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 = 
  ⊥-elim $ ¬Any[] (a∈l1→a∈l2  h1 $ here PE.refl)
free-eq {h1 ∷ t1} {h2 ∷ t2} f1 f2 a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 with h1∈l2 | h2∈l1 | compare h1 h2 
  where
    h1∈l2 = a∈l1→a∈l2 h1 (here PE.refl)
    h2∈l1 = a∈l2→a∈l1 h2 (here PE.refl)
free-eq {h1 ∷ t1} {h2 ∷ t2} f1 f2 a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 | here h1≡h2 | h2∈l1 | tri< h1<h2 ¬h1≡h2 _ =
  ⊥-elim $ ¬h1≡h2 h1≡h2
free-eq {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ min2 _ _) a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 | there h1∈t2 | h2∈l1 | tri< h1<h2 ¬h1≡h2 _ =
  ⊥-elim $ irrefl PE.refl $ transitive< h1<h2 (LA.lookup min2 h1∈t2)
free-eq {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ min1 _ ft1) f2@(∷-Free _ _ min2 _ ft2) a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 | _ | there h2∈t1 | tri≈ ¬h1<h2 h1≡h2 _ =
  ⊥-elim $ ¬h1<h2 (LA.lookup min1 h2∈t1)
free-eq {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ min1 _ ft1) f2@(∷-Free _ _ min2 _ ft2) a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 | there h1∈t2 | _ | tri≈ _ h1≡h2 ¬h2<h1 =
  ⊥-elim $ ¬h2<h1 (LA.lookup min2 h1∈t2)
free-eq {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ min1 _ ft1) f2@(∷-Free _ _ min2 _ ft2) a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 | here _ | here h2≡h1 | tri≈ _ h1≡h2 _ =
  let
    a∈t1⇔a∈t2 : (a : Carrier) → a ∈ t1 ⇔ a ∈ t2
    a∈t1⇔a∈t2 a = equivalence (a∈t1→a∈t2 a) (a∈t2→a∈t1 a)

    t1≡t2 : t1 ≡ t2
    t1≡t2 = free-eq ft1 ft2 a∈t1⇔a∈t2
  in
  PE.subst₂ (λ h → λ t → h1 ∷ t1 ≡ h ∷ t) h1≡h2 t1≡t2 PE.refl
  where
    a∈t1→a∈t2 : (a : Carrier) → (a ∈ t1) → (a ∈ t2)
    a∈t1→a∈t2 a a∈t1 with (a∈l1→a∈l2 a $ there a∈t1)
    a∈t1→a∈t2 a a∈t1 | here a≡h2 with PE.trans a≡h2 h2≡h1
    a∈t1→a∈t2 a a∈t1 | here a≡h2 | a≡h1@PE.refl =
      ⊥-elim $ irrefl PE.refl $ LA.lookup min1 a∈t1
    a∈t1→a∈t2 a a∈t1 | there a∈t2 =
      a∈t2

    a∈t2→a∈t1 : (a : Carrier) → (a ∈ t2) → (a ∈ t1)
    a∈t2→a∈t1 a a∈t2 with (a∈l2→a∈l1 a $ there a∈t2)
    a∈t2→a∈t1 a a∈t2 | here a≡h1 with PE.trans a≡h1 (PE.sym h2≡h1)
    a∈t2→a∈t1 a a∈t2 | here a≡h1 | a≡h2@PE.refl =
      ⊥-elim $ irrefl PE.refl $ LA.lookup min2 a∈t2
    a∈t2→a∈t1 a a∈t2 | there a∈t1 =
      a∈t1
free-eq {h1 ∷ t1} {h2 ∷ t2} f1 f2 a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 | h1∈l2 | here h2≡h1 | tri> _ ¬h1≡h2 h2<h1 =
  ⊥-elim $ ¬h1≡h2 (PE.sym h2≡h1)
free-eq {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ min1 _ _) f2 a∈l1⇔a∈l2 | a∈l2→a∈l1 | a∈l1→a∈l2 | h1∈l2 | there h2∈t1 | tri> _ ¬h1≡h2 h2<h1 =
  ⊥-elim $ irrefl PE.refl $ transitive< h2<h1 (LA.lookup min1 h2∈t1)

Carrier-FP : Set₁
Carrier-FP = Σ[ x ∈ List Carrier ] (IsFreeList _<_ _⊑_ x)

data _⋜_ : Carrier-FP → Carrier-FP → Set₁ where
  []-⋜ : {cfp : Carrier-FP} → ([] , []-Free) ⋜ cfp  
  cmp-⋜ : {h1 h2 : Carrier} {t1 t2 : List Carrier} → (ft1 : IsFreeList _<_ _⊑_ t1) →
          (f1 : IsFreeList _<_ _⊑_ (h1 ∷ t1)) →
          (f2 : IsFreeList _<_ _⊑_ (h2 ∷ t2)) →
          h1 ⊑ h2 →
          (t1 , ft1) ⋜ (h2 ∷ t2 , f2) →
          (h1 ∷ t1 , f1) ⋜ (h2 ∷ t2 , f2)
  skip-⋜ : {h1 h2 : Carrier} {t1 t2 : List Carrier} → 
            (f1 : IsFreeList _<_ _⊑_ (h1 ∷ t1)) → 
            (ft2 : IsFreeList _<_ _⊑_ t2) → 
            (f2 : IsFreeList _<_ _⊑_ (h2 ∷ t2)) →
            (h2 < h1) → (h1 ∥ h2) → (h1 ∷ t1 , f1) ⋜ (t2 , ft2) →
            (h1 ∷ t1 , f1) ⋜ (h2 ∷ t2 , f2)

_≤_ : (l1 l2 : Carrier-FP) → Set
(l1 , f1) ≤ (l2 , f2) = All (λ x → Any (x ⊑_) l2) l1

⋜→≤ : {l1 l2 : Carrier-FP} → (l1 ⋜ l2) → (l1 ≤ l2)
⋜→≤ {.([] , []-Free)} {l2} []-⋜ = 
  []
⋜→≤ {h1 ∷ t1 , f1} {h2 ∷ t2 , f2} (cmp-⋜ _ _ _ h1⊑h2 t1⋜l2) = 
  (here h1⊑h2) ∷ ⋜→≤ t1⋜l2
⋜→≤ {h1 ∷ t1 , f1} {h2 ∷ t2 , f2} (skip-⋜ _ _ _ h2<h1 h1∥h2 l1⋜t2) = 
  LA.map (λ x⊑t2 → there x⊑t2) (⋜→≤ l1⋜t2)

≤→⋜ : {l1 l2 : Carrier-FP} → (l1 ≤ l2) → (l1 ⋜ l2)
≤→⋜ {[] , []-Free} {l2 , f2} [] = 
  []-⋜
≤→⋜ {h1 ∷ t1 , f1@(∷-Free .h1 .t1 min1 incomp1 ft1)} {[] , []-Free} (h1⊑l2 ∷ t1≤l2) =
  ⊥-elim $ ¬Any[] h1⊑l2
≤→⋜ {h1 ∷ t1 , f1@(∷-Free .h1 .t1 min1 incomp1 ft1)} {l2@(h2 ∷ t2) , f2@(∷-Free _ _ _ _ ft2)} (h1⊑l2 ∷ t1≤l2) 
  with (≤→⋜ {t1 , ft1} {h2 ∷ t2 , f2} t1≤l2) 
≤→⋜ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {l2@(h2 ∷ t2) , f2} (here (h1⊑h2) ∷ t1≤l2) | t1⋜l2 =
  cmp-⋜ ft1 f1 f2 h1⊑h2 t1⋜l2
≤→⋜ {h1 ∷ t1 , ∷-Free .h1 .t1 _ _ _} {h2 ∷ t2 , ∷-Free .h2 .t2 min2 incomp2 _} h1⋜l2@(there h1⊑t2 ∷ t1≤l2) | t1⋜l2 with h1 ∦? h2
≤→⋜ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ _ _ _)} t1⋜l2@(there h1⊑t2 ∷ t1≤l2) | t1⋜l2 | l⊑r h1⊑h2 ¬h2⊑h1 =
   cmp-⋜ ft1 f1 f2 h1⊑h2 t1⋜l2 
≤→⋜ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ _ incomp2 _)} t1⋜l2@(there h1⊑t2 ∷ t1≤l2) | t1⋜l2 | r⊑l ¬h1⊑h2 h2⊑h1 =
 let
    eliminator : AnyEliminator Carrier ⊥ (h1 ⊑_) t2
    eliminator a f h1⊑a a∈t2 = incomp2 $ f (λ x → h2 ∦ x) (inj₁ $ transitive⊑ h2⊑h1 h1⊑a)
  in
  ⊥-elim $ anyEliminate t2 eliminator h1⊑t2
≤→⋜ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ _ _ _)} t1⋜l2@(there h1⊑t2 ∷ t1≤l2) | t1⋜l2 | l≡r h1≡h2 =
  cmp-⋜ ft1 f1 f2 (reflexive h1≡h2) t1⋜l2
≤→⋜ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ _ _ _)} t1⋜l2@(there h1⊑t2 ∷ t1≤l2) | t1⋜l2 | l∥r h1∥h2 with compare h1 h2
≤→⋜ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ min2 incomp2 _)} t1⋜l2@(there h1⊑t2 ∷ t1≤l2) | t1⋜l2 | l∥r h1∥h2 | tri< h1<h2 _ _ =
  let
    eliminator : AnyEliminator Carrier ⊥ (h1 ⊑_) t2
    eliminator a f h1⊑a a∈t2 = (unimodality h1<h2 (LA.lookup min2 a∈t2) (∦-refl h1) h1∥h2) (inj₁ h1⊑a)
  in
  ⊥-elim $ anyEliminate t2 eliminator h1⊑t2
≤→⋜ {h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ min2 incomp2 _)} t1⋜l2@(there h1⊑t2 ∷ t1≤l2) | t1⋜l2 | l∥r h1∥h2 | tri≈ _ h1≡h2@PE.refl _ =
  ⊥-elim $ h1∥h2 (∦-refl h1) 
≤→⋜ {h1 ∷ t1 , f1@(∷-Free _ _ min1 _ ft1)} {h2 ∷ t2 , f2@(∷-Free _ _ min2 incomp2 ft2)} l1⋜l2@(there h1⊑t2 ∷ t1≤l2) | t1⋜l2 | l∥r h1∥h2 | tri> _ _ h2<h1 =
  skip-⋜ f1 ft2 f2 h2<h1 h1∥h2 (≤→⋜ l1⋜t2)
  where
    p : Any (h1 ⊑_) t2
    p = h1⊑t2

    q : {x : Carrier} → x ∈ t1 → Any (x ⊑_) t2
    q {x} x∈t1 with (LA.lookup l1⋜l2 (there x∈t1))
    q {x} x∈t1 | (here x⊑h2) = ⊥-elim $ (unimodality h2<h1 h1<x (∦-refl h2) (∥-sym h1∥h2)) (inj₂ x⊑h2)
      where
        h1<x = LA.lookup min1 x∈t1
    q {x} x∈t1 | (there x⊑t2) = x⊑t2

    l1⋜t2 : All (λ x → Any (x ⊑_) t2) (h1 ∷ t1)
    l1⋜t2 = p ∷ (LA.tabulate q)

⋜⇔≤ : {a b : Carrier-FP} → (a ⋜ b ⇔ a ≤ b)
⋜⇔≤ =
  record
  { to = PE.→-to-⟶ ⋜→≤ 
  ; from = PE.→-to-⟶ ≤→⋜
  }

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

P∨ : {l1 l2 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → 
      (a : Carrier) → Set
P∨ {l1} {l2} f1 f2 a = (a ∈ l1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈ l1 × a ∈ l2)


a∈∨→P∨ : {l1 l2 l3 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → 
           (f3 : IsFreeList _<_ _⊑_ l3) → (l1 ∨ l2 ≡ l3) → {a : Carrier} → (a ∈ l3) → P∨ f1 f2 a

a∈∨→P∨ {[]} {[]} {.[]} f1 f2 f3 PE.refl {a} a∈l3 = 
  ⊥-elim $ ¬Any[] a∈l3
a∈∨→P∨ {[]} {h2 ∷ l2} {.(h2 ∷ l2)} f1 f2 f3 PE.refl {a} a∈l3 = 
  inj₂ $ inj₁ $ (a∈l3 , ¬Any[])
a∈∨→P∨ {h1 ∷ t1} {[]} {.(h1 ∷ t1)} f1 f2 f3 PE.refl {a} a∈l3 = 
  inj₁ $ (a∈l3 , ¬Any[])
a∈∨→P∨ {h1 ∷ t1} {h2 ∷ t2} {_} f1 f2 f3 PE.refl {a} a∈l3 with h1 ∦? h2
a∈∨→P∨ {l1@(h1 ∷ t1)} {l2@(h2 ∷ t2)} {_} f1@(∷-Free _ _ _ _ ft1) f2@(∷-Free _ _ min2 incomp2 _) f3 PE.refl {a} a∈l3 | l⊑r h1⊑h2 ¬h2⊑h1 = 
  let
    p : (a ∈ t1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) t1) ⊎ (a ∈ t1 × a ∈ l2) 
    p = a∈∨→P∨ ft1 f2 f3 PE.refl a∈l3
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
a∈∨→P∨ {l1@(h1 ∷ t1)} {l2@(h2 ∷ t2)} {_} f1@(∷-Free _ _ _ incomp1 _) f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} a∈l3 | r⊑l ¬h1⊑h2 h2⊑h1 = 
  let 
    p : (a ∈ l1 × ¬ Any (a ⊑_) t2) ⊎ (a ∈ t2 × ¬ Any (a ⊑_) l1) ⊎ (a ∈ l1 × a ∈ t2)
    p = (a∈∨→P∨ f1 ft2 f3 PE.refl a∈l3)
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
a∈∨→P∨ {l1@(h1 ∷ t1)} {l2@(.h1 ∷ t2)} {_} f1@(∷-Free _ _ _ _ ft1) f2@(∷-Free _ _ _ incomp2 _) f3 PE.refl {a} a∈l3 | l≡r h1≡h2@PE.refl = 
  let
    p : (a ∈ t1 × ¬ Any (a ⊑_) l2) ⊎ (a ∈ l2 × ¬ Any (a ⊑_) t1) ⊎ (a ∈ t1 × a ∈ l2) 
    p = (a∈∨→P∨ ft1 f2 f3 PE.refl a∈l3)
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

a∈∨→P∨ {h1 ∷ t1} {h2 ∷ t2} {_} f1 f2 f3 PE.refl {a} a∈l3 | l∥r h1∥h2 with compare h1 h2
a∈∨→P∨ {.a ∷ t1} {h2 ∷ t2} {_} f1 f2@(∷-Free _ _ min2 _ _) f3 PE.refl {a} (here a≡h1@PE.refl) | l∥r a∥h2 | tri< a<h2 _ _ =
  inj₁ $ ((here PE.refl) , ¬a⊑l2)
  where
    ¬a⊑l2 : ¬  Any (a ⊑_) (h2 ∷ t2)
    ¬a⊑l2 (here a⊑h2) = a∥h2 (inj₁ a⊑h2) 
    ¬a⊑l2 (there a⊑t2) = anyEliminate t2 eliminator a⊑t2
      where
        eliminator : AnyEliminator Carrier ⊥ (a ⊑_) t2
        eliminator x f a⊑x x∈t2 = (unimodality a<h2 (LA.lookup min2 x∈t2) (inj₁ $ reflexive {a} {a} PE.refl) a∥h2) (inj₁ a⊑x)
a∈∨→P∨ {l1@(h1 ∷ t1)} {l2@(h2 ∷ t2)} {_} f1@(∷-Free _ _ _ _ ft1) f2@(∷-Free _ _ min2 _ _) f3 PE.refl {a} (there a∈t1∨l2) | l∥r h1∥h2 | tri< h1<h2 _ _ =
  let 
    p = a∈∨→P∨ ft1 f2 (∨-free ft1 f2) PE.refl a∈t1∨l2
  in
    ([_,_] c1) ([_,_] c2 c3) p
  where
    c1 : (a ∈ t1 × ¬ Any (a ⊑_) l2) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c1 (a∈t1 , ¬a⊑l2) = inj₁ $ (there a∈t1 , ¬a⊑l2)

    c2 : (a ∈ l2 × ¬ Any (a ⊑_) t1) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c2 (here a≡h2@PE.refl , ¬a⊑t1) = 
      inj₂ $ inj₁ $ (here PE.refl , ¬a⊑l1)
      where
        ¬a⊑l1 : ¬ Any (a ⊑_) l1
        ¬a⊑l1 (here a⊑h1) = h1∥h2 (inj₂ a⊑h1)
        ¬a⊑l1 (there a⊑t1) = ¬a⊑t1 a⊑t1

    c2 (there a∈t2 , ¬a⊑t1) = 
      inj₂ $ inj₁ $ (there a∈t2 , ¬a⊑l1)
      where
        a∥h1 : a ∥ h1
        a∥h1 = ∥-sym $ unimodality h1<h2 (LA.lookup min2 a∈t2) (inj₁ $ reflexive {h1} {h1} PE.refl) h1∥h2

        ¬a⊑l1 : ¬ Any (a ⊑_) l1
        ¬a⊑l1 (here a⊑h1) = a∥h1 (inj₁ a⊑h1)
        ¬a⊑l1 (there a⊑t1) = ¬a⊑t1 a⊑t1

    c3 : (a ∈ t1 × a ∈ l2) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c3 (a∈t1 , a∈l2) = inj₂ $ inj₂ $ (there a∈t1 , a∈l2)
a∈∨→P∨ {h1 ∷ t1} {h2 ∷ t2} {_} f1 f2@(∷-Free _ _ min2 _ _) f3 PE.refl {a} a∈l3 | l∥r h1∥h2 | tri≈ _ h1≡h2 _ =
  ⊥-elim $ h1∥h2 (inj₁ $ reflexive h1≡h2)
a∈∨→P∨ {l1@(h1 ∷ t1)} {l2@(.a ∷ t2)} {_} f1@(∷-Free _ _ min1 _ _) f2 f3 PE.refl {a} (here a≡h2@PE.refl) | l∥r h1∥a | tri> _ _ a<h1 =
  inj₂ $ inj₁ $ ((here a≡h2) , ¬a⊑l1)
  where
    ¬a⊑l1 : ¬  Any (a ⊑_) (h1 ∷ t1)
    ¬a⊑l1 (here a⊑h1) = h1∥a (inj₂ a⊑h1) 
    ¬a⊑l1 (there a⊑t1) = anyEliminate t1 eliminator a⊑t1
      where
        eliminator : AnyEliminator Carrier ⊥ (a ⊑_) t1
        eliminator x f a⊑x x∈t1 = (unimodality a<h1 (LA.lookup min1 x∈t1) (inj₁ $ reflexive a≡h2) (∥-sym h1∥a)) (inj₁ a⊑x)
a∈∨→P∨ {l1@(h1 ∷ t1)} {l2@(h2 ∷ t2)} {_} f1@(∷-Free _ _ min1 _ _) f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} (there a∈l1∨t2) | l∥r h1∥h2 | tri> _ _ h2<h1 =
  let 
    p = a∈∨→P∨ f1 ft2 (∨-free f1 ft2) PE.refl a∈l1∨t2
  in
    ([_,_] c1) ([_,_] c2 c3) p
  where
    c1 : (a ∈ l1 × ¬ Any (a ⊑_) t2) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c1 (here a≡h1@PE.refl , ¬a⊑t2) =
      inj₁ $ (here PE.refl , ¬a⊑l2)
      where
        ¬a⊑l2 : ¬ Any (a ⊑_) l2
        ¬a⊑l2 (here a⊑h2) = h1∥h2 (inj₁ a⊑h2)
        ¬a⊑l2 (there a⊑t2) = ¬a⊑t2 a⊑t2
    c1 (there a∈t1 , ¬a⊑t2) = 
      inj₁ (there a∈t1 , ¬a⊑l2)
      where
        a∥h2 : a ∥ h2
        a∥h2 = ∥-sym $ unimodality h2<h1 (LA.lookup min1 a∈t1) (inj₁ $ reflexive {h2} {h2} PE.refl) (∥-sym h1∥h2)

        ¬a⊑l2 : ¬ Any (a ⊑_) l2
        ¬a⊑l2 (here a⊑h2) = a∥h2 (inj₁ a⊑h2)
        ¬a⊑l2 (there a⊑t2) = ¬a⊑t2 a⊑t2

    c2 : (a ∈ t2 × ¬ Any (a ⊑_) l1) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c2 (a∈t2 , ¬a⊑t1) = inj₂ $ inj₁ $ (there a∈t2 , ¬a⊑t1) 

    c3 : (a ∈ l1 × a ∈ t2) → (a ∈ l1 × ¬ Any (_⊑_ a) l2) ⊎ (a ∈ l2 × ¬ Any (_⊑_ a) l1) ⊎ (a ∈ l1 × a ∈ l2)
    c3 (a∈l1 , a∈t2) = inj₂ $ inj₂ $ (a∈l1 , there a∈t2)

P∨→a∈∨ : {l1 l2 l3 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → 
            (f3 : IsFreeList _<_ _⊑_ l3) → (l1 ∨ l2 ≡ l3) → {a : Carrier} → P∨ f1 f2 a → (a ∈ l3)

P∨→a∈∨ {[]} {l2} {.l2} f1 f2 f3 PE.refl {a} (inj₁ (a∈[] , ¬a⊑l2)) = ⊥-elim $ ¬Any[] a∈[]
P∨→a∈∨ {[]} {l2} {.l2} f1 f2 f3 PE.refl {a} (inj₂ (inj₁ (a∈l2 , ¬a⊑[]))) = a∈l2
P∨→a∈∨ {[]} {l2} {.l2} f1 f2 f3 PE.refl {a} (inj₂ (inj₂ (a∈[] , ¬a∈l2))) = ⊥-elim $ ¬Any[] a∈[]
P∨→a∈∨ {h1 ∷ t1} {[]} {.(h1 ∷ t1)} f1 f2 f3 PE.refl {a} (inj₁ (a∈l1 , ¬a⊑[])) = a∈l1
P∨→a∈∨ {h1 ∷ t1} {[]} {.(h1 ∷ t1)} f1 f2 f3 PE.refl {a} (inj₂ (inj₁ (a∈[] , ¬a⊑l1))) = ⊥-elim $ ¬Any[] a∈[]
P∨→a∈∨ {h1 ∷ t1} {[]} {.(h1 ∷ t1)} f1 f2 f3 PE.refl {a} (inj₂ (inj₂ (a∈l1 , ¬a⊑[]))) = a∈l1
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2 f3 PE.refl {a} P∨12a with h1 ∦? h2
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2 f3 PE.refl {a} (inj₁ (here a≡h1 , ¬a⊑l2)) | l⊑r h1⊑h2 ¬h2⊑h1 = 
  ⊥-elim $ ¬a⊑l2 $ here (transitive⊑ (reflexive a≡h1) h1⊑h2)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ _ ft1) f2 f3 PE.refl {a} (inj₁ (there a∈t1 , ¬a⊑l2)) | l⊑r h1⊑h2 ¬h2⊑h1 =
  P∨→a∈∨ ft1 f2 f3 PE.refl (inj₁ $ a∈t1 , ¬a⊑l2)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ _ ft1) f2 f3 PE.refl {a} (inj₂ (inj₁ (a∈l2 , ¬a⊑l1))) | l⊑r h1⊑h2 ¬h2⊑h1 = 
  P∨→a∈∨ ft1 f2 f3 PE.refl (inj₂ $ inj₁ $ a∈l2 , ¬a⊑t1)
  where
    ¬a⊑t1 : ¬ Any (a ⊑_) t1
    ¬a⊑t1 a⊑t1 = ¬a⊑l1 (there a⊑t1)
P∨→a∈∨ {.a ∷ t1} {h2 ∷ t2} {.((a ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ incomp1 ft1) f2 f3 PE.refl {a} (inj₂ (inj₂ (here a≡h1@PE.refl , a∈l2))) | l⊑r a⊑h2 ¬h2⊑a = 
  P∨→a∈∨ ft1 f2 f3 PE.refl (inj₂ $ inj₁ $ (a∈l2 , ¬a⊑t1))
  where
    ¬a⊑t1 : ¬ Any (a ⊑_) t1
    ¬a⊑t1 a⊑t1 = incomp1 $ LAny.map (λ a⊑t1 → inj₁ a⊑t1) a⊑t1
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ _ ft1) f2 f3 PE.refl {a} (inj₂ (inj₂ (there a∈t1 , a∈l2))) | l⊑r h1⊑h2 ¬h2⊑h1 =
  P∨→a∈∨ ft1 f2 f3 PE.refl (inj₂ $ inj₂ $ a∈t1 , a∈l2)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} (inj₁ (a∈l1 , ¬a⊑l2)) | r⊑l ¬h1⊑h2 h2⊑h1 =
  P∨→a∈∨ f1 ft2 f3 PE.refl (inj₁ $ a∈l1 , ¬a⊑t2)
  where
    ¬a⊑t2 : ¬ Any (a ⊑_) t2
    ¬a⊑t2 a⊑t2 = ¬a⊑l2 (there a⊑t2)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} (inj₂ (inj₁ (here a≡h2 , ¬a⊑l1))) | r⊑l ¬h1⊑h2 h2⊑h1 =
  ⊥-elim $ ¬a⊑l1 (here $ transitive⊑ (reflexive a≡h2) h2⊑h1)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} (inj₂ (inj₁ (there a∈t2 , ¬a⊑l1))) | r⊑l ¬h1⊑h2 h2⊑h1 =
  P∨→a∈∨ f1 ft2 f3 PE.refl (inj₂ $ inj₁ $ (a∈t2 , ¬a⊑l1))
P∨→a∈∨ {h1 ∷ t1} {.a ∷ t2} {.((h1 ∷ t1) ∨ (a ∷ t2))} f1 f2@(∷-Free _ _ _ incomp2 ft2) f3 PE.refl {a} (inj₂ (inj₂ (a∈l1 , here a≡h2@PE.refl))) | r⊑l ¬h1⊑a a⊑h1 =
  P∨→a∈∨ f1 ft2 f3 PE.refl (inj₁ $ a∈l1 , ¬a⊑t2)
  where
    ¬a⊑t2 : ¬ Any (a ⊑_) t2
    ¬a⊑t2 a⊑t2 = incomp2 $ LAny.map (λ a⊑x → inj₁ a⊑x) a⊑t2
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} (inj₂ (inj₂ (a∈l1 , there a∈t2))) | r⊑l ¬h1⊑h2 h2⊑h1 =
  P∨→a∈∨ f1 ft2 f3 PE.refl (inj₂ $ inj₂ $ a∈l1 , a∈t2)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2 f3 PE.refl {a} (inj₁ (here a≡h1 , ¬a⊑l2)) | l≡r h1≡h2 = 
  ⊥-elim $ ¬a⊑l2 $ here (transitive⊑ (reflexive a≡h1) (reflexive h1≡h2))
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ _ ft1) f2 f3 PE.refl {a} (inj₁ (there a∈t1 , ¬a⊑l2)) | l≡r h1≡h2 =
  P∨→a∈∨ ft1 f2 f3 PE.refl (inj₁ $ a∈t1 , ¬a⊑l2)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ _ ft1) f2 f3 PE.refl {a} (inj₂ (inj₁ (a∈l2 , ¬a⊑l1))) | l≡r h1≡h2 = 
  P∨→a∈∨ ft1 f2 f3 PE.refl (inj₂ $ inj₁ $ a∈l2 , ¬a⊑t1)
  where
    ¬a⊑t1 : ¬ Any (a ⊑_) t1
    ¬a⊑t1 a⊑t1 = ¬a⊑l1 (there a⊑t1)
P∨→a∈∨ {.a ∷ t1} {h2 ∷ t2} {.((a ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ incomp1 ft1) f2 f3 PE.refl {a} (inj₂ (inj₂ (here a≡h1@PE.refl , a∈l2))) | l≡r h1≡h2 = 
  P∨→a∈∨ ft1 f2 f3 PE.refl (inj₂ $ inj₁ $ (a∈l2 , ¬a⊑t1))
  where
    ¬a⊑t1 : ¬ Any (a ⊑_) t1
    ¬a⊑t1 a⊑t1 = incomp1 $ LAny.map (λ a⊑t1 → inj₁ a⊑t1) a⊑t1
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ _ ft1) f2 f3 PE.refl {a} (inj₂ (inj₂ (there a∈t1 , a∈l2))) | l≡r h1≡h2 =
  P∨→a∈∨ ft1 f2 f3 PE.refl (inj₂ $ inj₂ $ a∈t1 , a∈l2)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2 f3 PE.refl {a} P∨12a | l∥r h1∥h2 with compare h1 h2
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2 f3 PE.refl {a} (inj₁ (here a≡h1 , ¬a⊑l2)) | l∥r h1∥h2 | tri< h1<h2 _ _ = 
  here a≡h1
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ _ ft1) f2 f3 PE.refl {a} (inj₁ (there a∈t1 , ¬a⊑l2)) | l∥r h1∥h2 | tri< h1<h2 _ _ = 
  there $ P∨→a∈∨ ft1 f2 (∨-free ft1 f2) (LP.∷-injectiveʳ {x = h1} {xs = t1 ∨ (h2 ∷ t2)} PE.refl) (inj₁ (a∈t1 , ¬a⊑l2))
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ _ ft1) f2 f3 PE.refl {a} (inj₂ (inj₁ (a∈l2 , ¬a⊑l1))) | l∥r h1∥h2 | tri< h1<h2 _ _ = 
  there $ P∨→a∈∨ ft1 f2 (∨-free ft1 f2) (LP.∷-injectiveʳ {x = h1} {xs = t1 ∨ (h2 ∷ t2)} PE.refl) (inj₂ $ inj₁ $ a∈l2 , ¬a⊑t1)
  where
    ¬a⊑t1 : ¬ Any (a ⊑_) t1
    ¬a⊑t1 a⊑t1 = ¬a⊑l1 (there a⊑t1)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ _ ft1) f2 f3 PE.refl {a} (inj₂ (inj₂ (here a≡h1 , a∈l2))) | l∥r h1∥h2 | tri< h1<h2 _ _ = 
  here a≡h1
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1@(∷-Free _ _ _ _ ft1) f2 f3 PE.refl {a} (inj₂ (inj₂ (there a∈t1 , a∈l2))) | l∥r h1∥h2 | tri< h1<h2 _ _ = 
  there $ P∨→a∈∨ ft1 f2 (∨-free ft1 f2) (LP.∷-injectiveʳ {x = h1} {xs = t1 ∨ (h2 ∷ t2)} PE.refl) (inj₂ $ inj₂ $ a∈t1 , a∈l2)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2 f3 PE.refl {a} P∨12a | l∥r h1∥h2 | tri≈ _ h1≡h2 _ = 
  ⊥-elim $ h1∥h2 (inj₁ $ reflexive h1≡h2)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} (inj₁ (a∈l1 , ¬a⊑l2)) | l∥r h1∥h2 | tri> _ _ h2<h1 = 
  there $ P∨→a∈∨ f1 ft2 (∨-free f1 ft2) (LP.∷-injectiveʳ {x = h2} {xs = (h1 ∷ t1) ∨ t2} PE.refl) (inj₁ $ a∈l1 , ¬a⊑t2)
  where
    ¬a⊑t2 : ¬ Any (a ⊑_) t2
    ¬a⊑t2 a⊑t2 = ¬a⊑l2 (there a⊑t2)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} (inj₂ (inj₁ (here a≡h2 , ¬a⊑l1))) | l∥r h1∥h2 | tri> _ _ h2<h1 = 
  here a≡h2
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} (inj₂ (inj₁ (there a∈t2 , ¬a⊑l1))) | l∥r h1∥h2 | tri> _ _ h2<h1 = 
  there $ P∨→a∈∨ f1 ft2 (∨-free f1 ft2) (LP.∷-injectiveʳ {x = h2} {xs = (h1 ∷ t1) ∨ t2} PE.refl) (inj₂ $ inj₁ $ a∈t2 , ¬a⊑l1)
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} (inj₂ (inj₂ (a∈l1 , here a≡h2))) | l∥r h1∥h2 | tri> _ _ h2<h1 = 
  here a≡h2
P∨→a∈∨ {h1 ∷ t1} {h2 ∷ t2} {.((h1 ∷ t1) ∨ (h2 ∷ t2))} f1 f2@(∷-Free _ _ _ _ ft2) f3 PE.refl {a} (inj₂ (inj₂ (a∈l1 , there a∈t2))) | l∥r h1∥h2 | tri> _ _ h2<h1 = 
  there $ P∨→a∈∨ f1 ft2 (∨-free f1 ft2) (LP.∷-injectiveʳ {x = h2} {xs = (h1 ∷ t1) ∨ t2} PE.refl) (inj₂ $ inj₂ $ a∈l1 , a∈t2)


x∈∨⇔P∨ : {l1 l2 l3 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → 
            (f3 : IsFreeList _<_ _⊑_ l3) → (eq : l1 ∨ l2 ≡ l3) → (x : Carrier) → (x ∈ l3 ⇔ P∨ f1 f2 x)

x∈∨⇔P∨ {l1} {l2} {l3} f1 f2 f3 eq x =
  equivalence (a∈∨→P∨ f1 f2 f3 eq) (P∨→a∈∨ f1 f2 f3 eq)

⊥' : Carrier-FP
⊥' = ([] , []-Free)

_∨'_ : Carrier-FP → Carrier-FP → Carrier-FP
_∨'_ (l1 , f1) (l2 , f2) = (l1 ∨ l2 , ∨-free f1 f2) 

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

FP-Setoid : Setoid l1 l0
FP-Setoid = record
  { Carrier = Carrier-FP
  ; _≈_ = _≈_
  ; isEquivalence = ≈-isEquiv
  }

a≤b→a∨b≈b : (a b : Carrier-FP) → (a ≤ b) → (a ∨' b ≈ b)
a≤b→a∨b≈b a@(l1 , f1) b@(l2 , f2) a≤b = free-eq (∨-free f1 f2) f2 x∈∨⇔x∈l2
  where
    open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)

    x∈l2→P∨ : {x : Carrier} → (x ∈ l2) → P∨ f1 f2 x
    x∈l2→P∨ {x} x∈l2 with x ∈? l1
      where
        open DecSetoid ≡-decSetoid
    x∈l2→P∨ {x} x∈l2 | no ¬x∈l1 = inj₂ $ inj₁ $ x∈l2 , ¬x⊑l1
      where
        elim : AnyEliminator Carrier ⊥ (x ⊑_) l1
        elim z f x⊑z z∈l1 = anyEliminate l2 elim' (LA.lookup a≤b z∈l1)
          where
            elim' : AnyEliminator Carrier ⊥ (z ⊑_) l2
            elim' w f z⊑w w∈l2 = ¬x∈l1 $ PE.subst (λ x → x ∈ l1) z≡x z∈l1
              where
                x≡w : x ≡ w
                x≡w = free-incomp f2 x∈l2 w∈l2 (inj₁ $ transitive⊑ x⊑z z⊑w)

                z≡x : z ≡ x
                z≡x with x≡w
                z≡x | PE.refl = antisym z⊑w x⊑z

        ¬x⊑l1 : ¬ Any (x ⊑_) l1
        ¬x⊑l1 x⊑l1 = anyEliminate l1 elim x⊑l1
    x∈l2→P∨ {x} x∈l2 | yes x∈l1 = inj₂ $ inj₂ $ x∈l1 , x∈l2

    P∨→x∈l2 : {x : Carrier} → P∨ f1 f2 x → (x ∈ l2)
    P∨→x∈l2 {x} (inj₁ (x∈l1 , ¬x⊑l2)) = ⊥-elim $ ¬x⊑l2 (LA.lookup a≤b x∈l1) 
    P∨→x∈l2 {x} (inj₂ (inj₁ (x∈l2 , ¬x⊑l1))) = x∈l2
    P∨→x∈l2 {x} (inj₂ (inj₂ (x∈l1 , x∈l2))) = x∈l2

    P∨⇔x∈l2 : {x : Carrier} → P∨ f1 f2 x ⇔ (x ∈ l2)   
    P∨⇔x∈l2 = equivalence P∨→x∈l2 x∈l2→P∨

    x∈∨⇔x∈l2 : (x : Carrier) → x ∈ (l1 ∨ l2) ⇔ x ∈ l2 
    x∈∨⇔x∈l2 x = P∨⇔x∈l2 ∘ (x∈∨⇔P∨ f1 f2 (∨-free f1 f2) PE.refl x)

a∨b≈b→a≤b : (a b : Carrier-FP) → (a ∨' b ≈ b) → a ≤ b
a∨b≈b→a≤b ([] , f1) ([] , f2) a∨b≈b = []
a∨b≈b→a≤b ([] , f1) (h2 ∷ t2 , f2) a∨b≈b = []
a∨b≈b→a≤b (h1 ∷ t1 , f1) ([] , f2) ()
a∨b≈b→a≤b (h1 ∷ t1 , f1) (h2 ∷ t2 , f2) a∨b≈b with h1 ∦? h2
a∨b≈b→a≤b (l1@(h1 ∷ t1) , f1@(∷-Free _ _ _ _ ft1)) (l2@(h2 ∷ t2) , f2) a∨b≈b | l⊑r h1⊑h2 ¬h2⊑h1 =
  let
    t1≤l2 : (t1 , ft1) ≤ (l2 , f2)
    t1≤l2 = a∨b≈b→a≤b (t1 , ft1) (h2 ∷ t2 , f2) a∨b≈b
  in
  here h1⊑h2 ∷ t1≤l2
a∨b≈b→a≤b (l1@(h1 ∷ t1) , f1@(∷-Free _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-Free _ _ min2 incomp2 ft2)) a∨b≈b | r⊑l ¬h1⊑h2 h2⊑h1 rewrite PE.sym a∨b≈b =
  ⊥-elim contr
  where
    p : P∨ f1 ft2 h2
    p = a∈∨→P∨ f1 ft2 f2 a∨b≈b (here PE.refl)

    contr : ⊥
    contr with p
    contr | inj₁ (here h2≡h1 , _) =
      ¬h1⊑h2 $ reflexive (PE.sym h2≡h1)
    contr | inj₁ (there h2∈t1 , _) =
      incomp1 $ LAny.map (λ h2≡x → inj₂ $ transitive⊑ (reflexive $ PE.sym h2≡x) h2⊑h1) h2∈t1
    contr | inj₂ (inj₁ (h2∈t2 , _)) =
      incomp2 $ LAny.map (λ h2≡x → inj₁ $ reflexive h2≡x) h2∈t2
    contr | inj₂ (inj₂ (here h2≡h1 , _)) =
      ¬h1⊑h2 $ reflexive (PE.sym h2≡h1)
    contr | inj₂ (inj₂ (there h2∈t1 , _)) =
      incomp1 $ LAny.map (λ h2≡x → inj₂ $ transitive⊑ (reflexive $ PE.sym h2≡x) h2⊑h1) h2∈t1
a∨b≈b→a≤b (h1 ∷ t1 , f1@(∷-Free _ _ _ _ ft1)) (l2@(h2 ∷ t2) , f2) a∨b≈b | l≡r h1≡h2 =
  let
    t1≤l2 : (t1 , ft1) ≤ (l2 , f2)
    t1≤l2 = a∨b≈b→a≤b (t1 , ft1) (h2 ∷ t2 , f2) a∨b≈b
  in
  here (reflexive h1≡h2) ∷ t1≤l2
a∨b≈b→a≤b (h1 ∷ t1 , f1) (h2 ∷ t2 , f2) a∨b≈b | l∥r h1∥h2 with compare h1 h2
a∨b≈b→a≤b (l1@(h1 ∷ t1) , f1) (l2@(h2 ∷ t2) , f2) a∨b≈b | l∥r h1∥h2 | tri< h1<h2 _ _ =
  let 
    (h1≡h2 , t1∨l2≡t2) = ∷-injective a∨b≈b  
  in
  ⊥-elim $ h1∥h2 (inj₁ $ reflexive h1≡h2)
a∨b≈b→a≤b (h1 ∷ t1 , f1) (h2 ∷ t2 , f2) a∨b≈b | l∥r h1∥h2 | tri≈ _ h1≡h2 _ =
  ⊥-elim $ h1∥h2 (inj₁ $ reflexive h1≡h2) 
a∨b≈b→a≤b (l1@(h1 ∷ t1) , f1) (l2@(h2 ∷ t2) , f2@(∷-Free _ _ _ _ ft2)) a∨b≈b | l∥r h1∥h2 | tri> _ _ h2<h1 =
  let 
    (_ , l1∨t2≡t2) = ∷-injective a∨b≈b  
  in  
  LA.map (λ x⊑t2 → there x⊑t2) $ a∨b≈b→a≤b (l1 , f1) (t2 , ft2) l1∨t2≡t2

-- a.k.a. the connecting lemma
a∨b≈b⇔a≤b : (a b : Carrier-FP) → a ∨' b ≈ b ⇔ a ≤ b
a∨b≈b⇔a≤b a b = equivalence (a∨b≈b→a≤b a b) (a≤b→a∨b≈b a b)
 


a⊑b∨c→a⊑b⊎a⊑c : (a : Carrier) → {l1 l2 : List Carrier} → 
                   (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) →  
                   Any (a ⊑_) (l1 ∨ l2) → (Any (a ⊑_) l1) ⊎ (Any (a ⊑_) l2)

a⊑b∨c→a⊑b⊎a⊑c a {l1} {l2} f1 f2 a⊑l1∨l2 =
  anyEliminate (l1 ∨ l2) eliminator a⊑l1∨l2
  where
    eliminator : AnyEliminator Carrier ((Any (a ⊑_) l1) ⊎ (Any (a ⊑_) l2)) (a ⊑_) (l1 ∨ l2)
    eliminator x f a⊑x x∈l1∨l2 with P∨12x
      where
        open Equivalence (x∈∨⇔P∨ f1 f2 (∨-free f1 f2) PE.refl x)
        P∨12x : P∨ f1 f2 x
        P∨12x = to ⟨$⟩ x∈l1∨l2
    eliminator x f a⊑x x∈l1∨l2 | inj₁ (x∈l1 , ¬x⊑l2) = 
      inj₁ $ LAny.map (λ x≡· → transitive⊑ a⊑x (reflexive x≡·)) x∈l1
    eliminator x f a⊑x x∈l1∨l2 | inj₂ (inj₁ (x∈l2 , ¬x⊑l1)) = 
      inj₂ $ LAny.map (λ x≡· → transitive⊑ a⊑x (reflexive x≡·)) x∈l2
    eliminator x f a⊑x x∈l1∨l2 | inj₂ (inj₂ (x∈l1 , x∈l2)) = 
      inj₁ $ LAny.map (λ x≡· → transitive⊑ a⊑x (reflexive x≡·)) x∈l1

a⊑b⊎a⊑c→a⊑b∨c : (a : Carrier) → {l1 l2 : List Carrier} → 
                   (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) →  
                   (Any (a ⊑_) l1) ⊎ (Any (a ⊑_) l2) → Any (a ⊑_) (l1 ∨ l2)

a⊑b⊎a⊑c→a⊑b∨c a {[]} {l2} f1 f2 (inj₁ a⊑l1) = ⊥-elim $ ¬Any[] a⊑l1
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {[]} f1 f2 (inj₁ a⊑l1) = a⊑l1
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2 (inj₁ a⊑l1) with h1 ∦? h2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (inj₁ (here a⊑h1)) | l⊑r h1⊑h2 ¬h2⊑h1 = 
  a⊑b⊎a⊑c→a⊑b∨c a ft1 f2 $ inj₂ (here $ transitive⊑ a⊑h1 h1⊑h2)
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (inj₁ (there a⊑t1)) | l⊑r h1⊑h2 ¬h2⊑h1 =
  a⊑b⊎a⊑c→a⊑b∨c a ft1 f2 $ inj₁ a⊑t1
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) (inj₁ a⊑l1) | r⊑l ¬h1⊑h2 h2⊑h1 = 
  a⊑b⊎a⊑c→a⊑b∨c a f1 ft2 $ inj₁ a⊑l1
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (inj₁ (here a⊑h1)) | l≡r h1≡h2 = 
  a⊑b⊎a⊑c→a⊑b∨c a ft1 f2 $ inj₂ (here $ transitive⊑ a⊑h1 (reflexive h1≡h2))
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (inj₁ (there a⊑t1)) | l≡r h1≡h2 =
  a⊑b⊎a⊑c→a⊑b∨c a ft1 f2 $ inj₁ a⊑t1
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2 (inj₁ a⊑l1) | l∥r h1∥h2 with compare h1 h2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2 (inj₁ (here a⊑h1)) | l∥r h1∥h2 | tri< h1<h2 _ _ =
  here a⊑h1
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (inj₁ (there a⊑t1)) | l∥r h1∥h2 | tri< h1<h2 _ _ =
  there $ a⊑b⊎a⊑c→a⊑b∨c a ft1 f2 $ inj₁ a⊑t1
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2 (inj₁ a⊑l1) | l∥r h1∥h2 | tri≈ _ h1≡h2 _ =
  ⊥-elim $ h1∥h2 (inj₁ $ reflexive h1≡h2) 
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) (inj₁ a⊑l1) | l∥r h1∥h2 | tri> _ _ h2<h1 =
  there $ a⊑b⊎a⊑c→a⊑b∨c a f1 ft2 $ inj₁ a⊑l1
a⊑b⊎a⊑c→a⊑b∨c a {[]} {l2} f1 f2 (inj₂ a⊑l2) = a⊑l2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {[]} f1 f2 (inj₂ a⊑l2) = ⊥-elim $ ¬Any[] a⊑l2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2 (inj₂ a⊑l2) with h1 ∦? h2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (inj₂ a⊑l2) | l⊑r h1⊑h2 ¬h2⊑h1 = 
  a⊑b⊎a⊑c→a⊑b∨c a ft1 f2 $ inj₂ a⊑l2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) (inj₂ (here a⊑h2)) | r⊑l ¬h1⊑h2 h2⊑h1 = 
  a⊑b⊎a⊑c→a⊑b∨c a f1 ft2 $ inj₁ (here $ transitive⊑ a⊑h2 h2⊑h1)
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) (inj₂ (there a⊑t2)) | r⊑l ¬h1⊑h2 h2⊑h1 =
  a⊑b⊎a⊑c→a⊑b∨c a f1 ft2 $ inj₂ a⊑t2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (inj₂ a⊑l2) | l≡r h1≡h2 = 
  a⊑b⊎a⊑c→a⊑b∨c a ft1 f2 $ inj₂ a⊑l2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2 (inj₂ a⊑l1) | l∥r h1∥h2 with compare h1 h2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (inj₂ a⊑l2) | l∥r h1∥h2 | tri< h1<h2 _ _ =
  there $ a⊑b⊎a⊑c→a⊑b∨c a ft1 f2 $ inj₂ a⊑l2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2 (inj₂ a⊑l1) | l∥r h1∥h2 | tri≈ _ h1≡h2 _ =
  ⊥-elim $ h1∥h2 (inj₁ $ reflexive h1≡h2) 
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) (inj₂ (here a⊑h2)) | l∥r h1∥h2 | tri> _ _ h2<h1 =
  here a⊑h2
a⊑b⊎a⊑c→a⊑b∨c a {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) (inj₂ (there a⊑t2)) | l∥r h1∥h2 | tri> _ _ h2<h1 =
  there $ a⊑b⊎a⊑c→a⊑b∨c a f1 ft2 $ inj₂ a⊑t2 

a⊑b∨c⇔a⊑b⊎a⊑c : (a : Carrier) → {b c : List Carrier} → (fb : IsFreeList _<_ _⊑_ b) → (fc : IsFreeList _<_ _⊑_ c) → 
                   (Any (a ⊑_) (b ∨ c)) ⇔ ((Any (a ⊑_) b) ⊎ (Any (a ⊑_) c))
a⊑b∨c⇔a⊑b⊎a⊑c a fb fc = equivalence (a⊑b∨c→a⊑b⊎a⊑c a fb fc) (a⊑b⊎a⊑c→a⊑b∨c a fb fc)
