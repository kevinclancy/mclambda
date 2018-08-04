open import Function using (_$_)
open import Function.Equivalence as FE
open import Function.Equality using (_⟨$⟩_)
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

module FreeSemilattice.Semilattice (P : DeltaPoset0) where

open import FreeSemilattice.Core P renaming (_≤_ to _≤'_ ; _≈_ to _≈'_)
open import FreeSemilattice.Poset P as PS

open DeltaPoset0 P

infix 4 _≈_ _≤_
infixr 6 _∨'_
infixr 6 _∨_

private
 -- redeclared to control fixity relative to join operators
 _≤_ = _≤'_
 _≈_ = _≈'_

↓ : (p : Carrier) → List Carrier
↓ p = p ∷ []

-- unit of the free/forgetful adjunction
η : (p : Carrier) → Carrier-FP
η p = (↓ p , ∷-Free p [] [] (λ ()) []-Free)

∨-unitʳ : (l : List Carrier) → l ∨ [] ≡ l
∨-unitʳ [] = PE.refl
∨-unitʳ (x ∷ l) = PE.refl

∨-unitˡ : (l : List Carrier) → [] ∨ l ≡ l
∨-unitˡ [] = PE.refl
∨-unitˡ (x ∷ l) = PE.refl

⊥'-min :  Minimum _≤_ ⊥'
⊥'-min x = []

∨'-unitʳ : (s : Carrier-FP) → (s ∨' ⊥' ≈ s)
∨'-unitʳ (l , f) = ∨-unitʳ l

∨'-unitˡ : (s : Carrier-FP) → (⊥' ∨' s ≈ s) 
∨'-unitˡ (l , f) = ∨-unitˡ l

∨-discardˡ : (h1 h2 : Carrier) → (t1 t2 : List Carrier) → (h1 ⊑ h2) →
              ((h1 ∷ t1) ∨ (h2 ∷ t2) ≡ t1 ∨ (h2 ∷ t2))
∨-discardˡ h1 h2 t1 t2 h1⊑h2 with h1 ∦? h2
∨-discardˡ h1 h2 t1 t2 h1⊑h2 | l⊑r _ ¬h2⊑h1 = PE.refl
∨-discardˡ h1 h2 t1 t2 h1⊑h2 | r⊑l ¬h1⊑h2 _ = ⊥-elim $ ¬h1⊑h2 h1⊑h2
∨-discardˡ h1 h2 t1 t2 h1⊑h2 | l≡r PE.refl = PE.refl
∨-discardˡ h1 h2 t1 t2 h1⊑h2 | l∥r h1∥h2 = ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)

∨'-discardˡ : (h1 h2 : Carrier) → (t1 t2 : List Carrier) →
              {f1 : IsFreeList _<_ _⊑_ (h1 ∷ t1)} → {f2 : IsFreeList _<_ _⊑_ (h2 ∷ t2)} →
              {ft1 : IsFreeList _<_ _⊑_ t1} →
              (h1 ⊑ h2) → (h1 ∷ t1 , f1) ∨' (h2 ∷ t2 , f2) ≈ (t1 , ft1) ∨' (h2 ∷ t2 , f2)
∨'-discardˡ h1 h2 t1 t2 {f1} {f2} {ft1} h1⊑h2 = ∨-discardˡ h1 h2 t1 t2 h1⊑h2 

∨-pushˡ : ∀ {h : Carrier} → {l1 l2 : List Carrier} → (All (h <_) l1) → ¬ (Any (h ∦_) l1) → (All (h <_) l2) → ¬ (Any (h ∦_) l2) → (h ∷ (l1 ∨ l2) ≡ ((h ∷ l1) ∨ l2))
∨-pushˡ {h} {l1} {[]} min1 incomp1 min2 incomp2 rewrite (∨-unitʳ l1) = PE.refl
∨-pushˡ {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 with h ∦? h2
∨-pushˡ {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | l⊑r h⊑h2 ¬h2⊑h = ⊥-elim $ incomp2 (here $ inj₁ h⊑h2)
∨-pushˡ {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | r⊑l ¬h⊑h2 h2⊑h = ⊥-elim $ incomp2 (here $ inj₂ h2⊑h)
∨-pushˡ {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | l≡r h≡h2@PE.refl = ⊥-elim $ incomp2 (here $ inj₁ (reflexive PE.refl))
∨-pushˡ {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | l∥r h∥h2 with h <? h2
∨-pushˡ {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | l∥r h∥h2 | yes h<h2 = PE.refl
∨-pushˡ {h} {l1} {h2 ∷ l2} min1 incomp1 min2 incomp2 | l∥r h∥h2 | no ¬h<h2 = ⊥-elim $ ¬h<h2 (head min2)

∨-comm : {l1 l2 : List Carrier} → IsFreeList _<_ _⊑_ l1 → IsFreeList _<_ _⊑_ l2 → (l1 ∨ l2) ≡ (l2 ∨ l1)
∨-comm {[]} {k} f1 f2 = PE.sym (∨-unitʳ k)
∨-comm {h1 ∷ t1} {[]} f1 f2 = PE.refl
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 with h1 ∦? h2
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l⊑r h1⊑h2 ¬h2⊑h1 with h2 ∦? h1
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l⊑r h1⊑h2 ¬h2⊑h1 | l⊑r h2⊑h1 ¬h1⊑h2 = ⊥-elim $ ¬h1⊑h2 h1⊑h2
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 | l⊑r h1⊑h2 ¬h2⊑h1 | DeltaPoset0.r⊑l x x₁ = ∨-comm ft1 f2
∨-comm {h1 ∷ t1} {_ ∷ t2} f1@(∷-Free _ _ min1 incomp1 ft1) f2@(∷-Free _ _ min2 incomp2 ft2) | l⊑r h1⊑h2 ¬h2⊑h1 | DeltaPoset0.l≡r h1≡h2@PE.refl = 
    begin
    t1 ∨ (h1 ∷ t2) ≡⟨ ∨-comm ft1 f2 ⟩
    (h1 ∷ t2) ∨ t1 ≡⟨ PE.sym $ ∨-pushˡ min2 incomp2 min1 incomp1 ⟩
    h1 ∷ (t2 ∨ t1) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm ft2 ft1 ⟩
    h1 ∷ (t1 ∨ t2) ≡⟨ ∨-pushˡ min1 incomp1 min2 incomp2 ⟩
    (h1 ∷ t1) ∨ t2 ≡⟨ ∨-comm f1 ft2 ⟩
    t2 ∨ (h1 ∷ t1)
    ∎
    where
    open PE.≡-Reasoning
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r h2∥h1 = ⊥-elim $ h2∥h1 (inj₂ h1⊑h2) 
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | r⊑l ¬h1⊑h2 h2⊑h1 with h2 ∦? h1
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) | r⊑l ¬h1⊑h2 h2⊑h1 | l⊑r _ _ = ∨-comm f1 ft2
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | r⊑l ¬h1⊑h2 h2⊑h1 | r⊑l ¬h2⊑h1 h1⊑h2 = ⊥-elim $ ¬h1⊑h2 h1⊑h2
∨-comm {h1 ∷ t1} {.h1 ∷ t2} f1 f2 | r⊑l ¬h1⊑h1 h1⊑h1 | l≡r h1≡h2@PE.refl = ⊥-elim $ ¬h1⊑h1 h1⊑h1
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | DeltaPoset0.r⊑l ¬h1⊑h2 h2⊑h1 | l∥r h1∥h2 = ⊥-elim $ h1∥h2 (inj₁ h2⊑h1)
∨-comm {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l≡r h1≡h2@PE.refl with h1 ∦? h1 
∨-comm {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l≡r h1≡h2@PE.refl | l⊑r h1⊑h1 ¬h1⊑h1 = ⊥-elim $ ¬h1⊑h1 h1⊑h1
∨-comm {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l≡r h1≡h2@PE.refl | r⊑l ¬h1⊑h1 h1⊑h1 = ⊥-elim $ ¬h1⊑h1 h1⊑h1
∨-comm {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l≡r h1≡h2@PE.refl | l≡r _ = 
    begin
    t1 ∨ (h1 ∷ t2) ≡⟨ ∨-comm ft1 f2 ⟩
    (h1 ∷ t2) ∨ t1 ≡⟨ PE.sym $ ∨-pushˡ min2 incomp2 min1 incomp1 ⟩
    h1 ∷ (t2 ∨ t1) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm ft2 ft1 ⟩
    h1 ∷ (t1 ∨ t2) ≡⟨ ∨-pushˡ min1 incomp1 min2 incomp2 ⟩
    (h1 ∷ t1) ∨ t2 ≡⟨ ∨-comm f1 ft2 ⟩
    t2 ∨ (h1 ∷ t1)
    ∎
    where
    open PE.≡-Reasoning

∨-comm {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l≡r h1≡h2@PE.refl | l∥r h1∥h1 = ⊥-elim $ h1∥h1 (∦-refl h1)
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 with h1 <? h2 
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 | yes h1<h2 with h2 ∦? h1
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 | yes h1<h2 | l⊑r h2⊑h1 ¬h1⊑h2 = ⊥-elim $ h1∥h2 (inj₂ h2⊑h1)
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 | yes h1<h2 | r⊑l ¬h2⊑h1 h1⊑h2 = ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)
∨-comm {h1 ∷ t1} {.h1 ∷ t2} f1 f2 | l∥r h1∥h1 | yes h1<h1 | l≡r h1≡h2@PE.refl = ⊥-elim $ h1∥h1 (∦-refl h1)
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 | yes h1<h2 | l∥r h2∥h1 with h2 <? h1 
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 | yes h1<h2 | l∥r h2∥h1 | yes h2<h1 with h1≡h2 
    where 
    h1≡h2 : h1 ≡ h2
    h1≡h2 with compare h1 h2
    h1≡h2 | tri< _ _ ¬h2<h1 = ⊥-elim $ ¬h2<h1 h2<h1
    h1≡h2 | tri≈ _ h1≡h2 _ = h1≡h2
    h1≡h2 | tri> ¬h1<h2 _ _ = ⊥-elim $ ¬h1<h2 h1<h2
∨-comm {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l∥r h1∥h1 | yes h1<h1 | l∥r _ | yes _ | PE.refl = 
    begin
    h1 ∷ (t1 ∨ (h1 ∷ t2)) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm ft1 f2 ⟩
    h1 ∷ ((h1 ∷ t2) ∨ t1) ≡⟨ PE.cong (λ x → h1 ∷ x) $ PE.sym (∨-pushˡ min2 incomp2 min1 incomp1) ⟩
    h1 ∷ h1 ∷ (t2 ∨ t1) ≡⟨ PE.cong (λ x → h1 ∷ h1 ∷ x) $ ∨-comm ft2 ft1 ⟩
    h1 ∷ h1 ∷ (t1 ∨ t2) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-pushˡ min1 incomp1 min2 incomp2 ⟩
    h1 ∷ ((h1 ∷ t1) ∨ t2) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-comm f1 ft2 ⟩ 
    h1 ∷ (t2 ∨ (h1 ∷ t1))
    ∎
    where
    open PE.≡-Reasoning
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h2 .t2 min2 incomp2 ft2) | l∥r h1∥h2 | yes h1<h2 | l∥r h2∥h1 | no ¬h2<h1 = 
    PE.cong (λ x → h1 ∷ x) $ ∨-comm ft1 f2
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 | no ¬h1<h2 with h2 ∦? h1 
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 | no ¬h1<h2 | l⊑r h2⊑h1 ¬h1⊑h2 = ⊥-elim $ h1∥h2 (inj₂ h2⊑h1)
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 | no ¬h1<h2 | r⊑l ¬h2⊑h1 h1⊑h2 = ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)
∨-comm {.h2 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h2∥h2 | no ¬h2<h2 | l≡r h2≡h1@PE.refl = ⊥-elim $ h2∥h2 (∦-refl h2) 
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 | no ¬h1<h2 | l∥r _ with h2 <? h1
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free .h2 .t2 min2 incomp2 ft2) | l∥r h1∥h2 | no ¬h1<h2 | l∥r _ | yes h2<h1 = 
    PE.cong (λ x → h2 ∷ x) $ ∨-comm f1 ft2 
∨-comm {h1 ∷ t1} {h2 ∷ t2} f1 f2 | l∥r h1∥h2 | no ¬h1<h2 | l∥r _ | no ¬h2<h1 with h1≡h2 
    where
    h1≡h2 : h1 ≡ h2
    h1≡h2 with compare h1 h2
    h1≡h2 | tri< h1<h2 _ _ = ⊥-elim $ ¬h1<h2 h1<h2
    h1≡h2 | tri≈ _ goal _ = goal
    h1≡h2 | tri> _ _ h2<h1 = ⊥-elim $ ¬h2<h1 h2<h1
∨-comm {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free .h1 .t1 min1 incomp1 ft1) f2@(∷-Free .h1 .t2 min2 incomp2 ft2) | l∥r h1∥h1 | no ¬h1<h1 | l∥r _ | no _ | PE.refl =
    begin
    h1 ∷ ((h1 ∷ t1) ∨ t2) ≡⟨ PE.cong (λ x → h1 ∷ x) $ PE.sym (∨-pushˡ min1 incomp1 min2 incomp2) ⟩
    h1 ∷ h1 ∷ (t1 ∨ t2) ≡⟨ PE.cong (λ x → h1 ∷ h1 ∷ x) $ ∨-comm ft1 ft2 ⟩
    h1 ∷ h1 ∷ (t2 ∨ t1) ≡⟨ PE.cong (λ x → h1 ∷ x) $ ∨-pushˡ min2 incomp2 min1 incomp1 ⟩
    h1 ∷ ((h1 ∷ t2) ∨ t1)
    ∎
    where
      open PE.≡-Reasoning

∨'-comm : (s1 s2 : Carrier-FP) → (s1 ∨' s2 ≈ s2 ∨' s1)
∨'-comm (l1 , f1) (l2 , f2) = ∨-comm f1 f2

∨-pushʳ : ∀ {h : Carrier} → {l1 l2 : List Carrier} → (IsFreeList _<_ _⊑_ l1) → (IsFreeList _<_ _⊑_ l2) → (All (h <_) l1) → ¬ (Any (h ∦_) l1) → (All (h <_) l2) → ¬ (Any (h ∦_) l2) → (h ∷ (l1 ∨ l2) ≡ (l1 ∨ (h ∷ l2)))
∨-pushʳ {h} {l1} {l2} f1 f2 h<l1 h∥l1 h<l2 h∥l2 =
  let
    f-h∷l2 : IsFreeList _<_ _⊑_ (h ∷ l2)
    f-h∷l2 = ∷-Free h l2 h<l2 h∥l2 f2
  in
   begin
     h ∷ (l1 ∨ l2) ≡⟨ PE.cong (λ x → h ∷ x) $ ∨-comm f1 f2 ⟩
     h ∷ (l2 ∨ l1) ≡⟨ ∨-pushˡ h<l2 h∥l2 h<l1 h∥l1 ⟩
     ((h ∷ l2) ∨ l1) ≡⟨ ∨-comm f-h∷l2 f1 ⟩ 
     (l1 ∨ (h ∷ l2))
    ∎
  where
    open PE.≡-Reasoning

∨-discardʳ : {h1 h2 : Carrier} → {t1 t2 : List Carrier} → IsFreeList _<_ _⊑_ (h1 ∷ t1) → IsFreeList _<_ _⊑_ (h2 ∷ t2) → (h2 ⊑ h1) →
                ((h1 ∷ t1) ∨ (h2 ∷ t2) ≡ (h1 ∷ t1) ∨ t2)
∨-discardʳ {h1} {h2} {t1} {t2} f1 f2@(∷-Free _ _ _ _ ft2) h2⊑h1 =
    begin
    (h1 ∷ t1) ∨ (h2 ∷ t2) ≡⟨ ∨-comm f1 f2 ⟩
    (h2 ∷ t2) ∨ (h1 ∷ t1) ≡⟨ ∨-discardˡ h2 h1 t2 t1 h2⊑h1  ⟩
    t2 ∨ (h1 ∷ t1) ≡⟨ ∨-comm ft2 f1 ⟩
    (h1 ∷ t1) ∨ t2
    ∎
    where
    open PE.≡-Reasoning

∨-any-⊑ˡ : {x : Carrier} → {l1 l2 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → (Any (x ⊑_) l1) → (Any (x ⊑_) (l1 ∨ l2))
∨-any-⊑ˡ {x} {[]} {l2} f1 f2 p = ⊥-elim $ LAP.¬Any[] p
∨-any-⊑ˡ {x} {h1 ∷ t1} {[]} f1 f2 (here px) = here px
∨-any-⊑ˡ {x} {h1 ∷ t1} {[]} f1 f2 (there p) = there p 
∨-any-⊑ˡ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2 p with h1 ∦? h2
∨-any-⊑ˡ {x} {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (here px) | l⊑r h1⊑h2 ¬h2⊑h1 rewrite (∨-comm ft1 f2) = 
    ∨-any-⊑ˡ f2 ft1 (here (transitive⊑ px h1⊑h2))
∨-any-⊑ˡ {x} {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (there p) | l⊑r h1⊑h2 ¬h2⊑h1 = 
    ∨-any-⊑ˡ ft1 f2 p
∨-any-⊑ˡ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) p | r⊑l ¬h1⊑h2 h2⊑h1 = 
    ∨-any-⊑ˡ f1 ft2 p
∨-any-⊑ˡ {x} {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (here px) | l≡r PE.refl rewrite (∨-comm ft1 f2) = 
    ∨-any-⊑ˡ f2 ft1 (here px)
∨-any-⊑ˡ {x} {h1 ∷ t1} {.h1 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (there p) | l≡r PE.refl = 
    ∨-any-⊑ˡ ft1 f2 p
∨-any-⊑ˡ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2 p | l∥r h1∥h2 with compare h1 h2 
∨-any-⊑ˡ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2 (here px) | l∥r h1∥h2 | tri< h1<h2 _ _ = 
    here px
∨-any-⊑ˡ {x} {h1 ∷ t1} {h2 ∷ t2} f1@(∷-Free _ _ _ _ ft1) f2 (there p) | l∥r h1∥h2 | tri< h1<h2 _ _ = 
    there (∨-any-⊑ˡ ft1 f2 p)
∨-any-⊑ˡ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2 p | l∥r h1∥h2 | tri≈ _ h1≡h2@PE.refl _ = 
    ⊥-elim $ h1∥h2 (∦-refl h1)
∨-any-⊑ˡ {x} {h1 ∷ t1} {h2 ∷ t2} f1 f2@(∷-Free _ _ _ _ ft2) p | l∥r h1∥h2 | tri> _ _ h2<h1 = 
    there (∨-any-⊑ˡ f1 ft2 p)

∨-any-⊑ʳ : {x : Carrier} → {l1 l2 : List Carrier} → (f1 : IsFreeList _<_ _⊑_ l1) → (f2 : IsFreeList _<_ _⊑_ l2) → (Any (x ⊑_) l2) → (Any (x ⊑_) (l1 ∨ l2))
∨-any-⊑ʳ {x} {l1} {l2} f1 f2 x⊑l2 rewrite ∨-comm f1 f2 = ∨-any-⊑ˡ f2 f1 x⊑l2 

incomp-lemma : {h1 h2 : Carrier} → {t2 : List Carrier} → (h1<h2 : h1 < h2) → (min2 : All (h2 <_) t2) → (h1∥h2 : h1 ∥ h2) → ¬ (Any (h1 ∦_) (h2 ∷ t2))
incomp-lemma {h1} {h2} {t2} h1<h2 min2 h1∥h2 (here h1∦h2) = h1∥h2 h1∦h2
incomp-lemma {h1} {h2} {t2} h1<h2 min2 h1∥h2 (there h1∦t2) = anyEliminate t2 eliminator h1∦t2 
    where
    eliminator : AnyEliminator Carrier ⊥ (h1 ∦_) t2
    eliminator a f h1∦a a∈t2 = (unimodality h1<h2 (LA.lookup min2 a∈t2) (∦-refl h1) h1∥h2) h1∦a

∨'-monoˡ : {a b : Carrier-FP} → (c : Carrier-FP) → a ≤ b → a ∨' c ≤ b ∨' c
∨'-monoˡ {a , fa} {b , fb} (c , fc) a≤b =
  LA.tabulate x∈a∨c→x⊑b∨c
  where
    x∈a∨c→x⊑b∨c : {x : Carrier} → (x ∈ a ∨ c) → Any (x ⊑_) (b ∨ c)
    x∈a∨c→x⊑b∨c {x} x∈a∨c with to ⟨$⟩ x∈a∨c 
      where
        open Equivalence (x∈∨⇔P∨ fa fc (PE.subst (IsFreeList _<_ _⊑_) PE.refl (∨-free fa fc)) PE.refl x)
    x∈a∨c→x⊑b∨c {x} x∈a∨c | inj₁ (x∈a , ¬x⊑c) = from ⟨$⟩ inj₁ (LA.lookup a≤b x∈a)  
      where
        open Equivalence (a⊑b∨c⇔a⊑b⊎a⊑c x fb fc)
    x∈a∨c→x⊑b∨c {x} x∈a∨c | inj₂ (inj₁ (x∈c , ¬x⊑a)) =
      from ⟨$⟩ inj₂ (LAny.map (λ x≡· → reflexive x≡·) x∈c)
      where
        open Equivalence (a⊑b∨c⇔a⊑b⊎a⊑c x fb fc)
    x∈a∨c→x⊑b∨c {x} x∈a∨c | inj₂ (inj₂ (x∈a , x∈c)) =
      from ⟨$⟩ inj₂ (LAny.map (λ x≡· → reflexive x≡·) x∈c)
      where
        open Equivalence (a⊑b∨c⇔a⊑b⊎a⊑c x fb fc)

∨'-monoʳ : {a b : Carrier-FP} → (c : Carrier-FP) → a ≤ b → c ∨' a ≤ c ∨' b
∨'-monoʳ {a , fa} {b , fb} (c , fc) a≤b rewrite ∨'-comm (c , fc) (a , fa) | ∨'-comm (c , fc) (b , fb)  =
  ∨'-monoˡ {a , fa} {b , fb} (c , fc) a≤b

∨'-sup : Supremum _≤_ _∨'_ 
∨'-sup (x , fx) (y , fy) = (x≤x∨y , (y≤x∨y , x≤z∧y≤z→x∨y≤z))
  where
    open import Relation.Binary.PartialOrderReasoning FP-Poset0

    x≤x∨y : (x , fx) ≤ (x , fx) ∨' (y , fy)
    x≤x∨y = 
      begin
        (x , fx) ≈⟨ PE.sym $ ∨-unitʳ x ⟩
        (x ∨ [] , ∨-free fx []-Free) ≤⟨ ∨'-monoʳ {[] , []-Free} {y , fy} (x , fx) (⊥'-min $ y , fy) ⟩
        (x ∨ y , ∨-free fx fy)
       ∎

    y≤x∨y : (y , fy) ≤ (x , fx) ∨' (y , fy)
    y≤x∨y = 
      begin
        (y , fy) ≈⟨ PE.sym $ ∨-unitˡ y ⟩
        ([] ∨ y , ∨-free []-Free fy) ≤⟨ ∨'-monoˡ {[] , []-Free} {x , fx} (y , fy) (⊥'-min $ x , fx) ⟩
        (x ∨ y , ∨-free fx fy)
       ∎    

    x≤z∧y≤z→x∨y≤z : (z : Carrier-FP) → (x , fx) ≤ z → (y , fy) ≤ z → (x , fx) ∨' (y , fy) ≤ z
    x≤z∧y≤z→x∨y≤z (z , fz) x≤z y≤z = LA.tabulate q∈x∨y→q⊑z 
      where
        q∈x∨y→q⊑z : {q : Carrier} → (q ∈ x ∨ y) → Any (q ⊑_) z
        q∈x∨y→q⊑z {q} q∈x∨y with to ⟨$⟩ q∈x∨y
          where
            open Equivalence (x∈∨⇔P∨ fx fy (∨-free fx fy) PE.refl q)
        q∈x∨y→q⊑z {q} q∈x∨y | inj₁ (q∈x , ¬q⊑y) = 
          LA.lookup x≤z q∈x
        q∈x∨y→q⊑z {q} q∈x∨y | inj₂ (inj₁ (q∈y , ¬q⊑x)) =
          LA.lookup y≤z q∈y
        q∈x∨y→q⊑z {q} q∈x∨y | inj₂ (inj₂ (q∈x , q∈y)) =
          LA.lookup x≤z q∈x
        

isJoinSemilattice-≤-∨' : IsJoinSemilattice _≈_ _≤_ _∨'_
isJoinSemilattice-≤-∨' = record
  { isPartialOrder = Poset.isPartialOrder FP-Poset0
  ; supremum = ∨'-sup
  }

isBoundedJoinSemilattice-≤-∨' : IsBoundedJoinSemilattice _≈_ _≤_ _∨'_ ⊥'
isBoundedJoinSemilattice-≤-∨' = record
  { isJoinSemilattice = isJoinSemilattice-≤-∨'
  ; minimum = ⊥'-min 
  }

-- the "free semilattice" functor F produces a bounded join semilattice when applied to a delta poset
FP-BJS : BoundedJoinSemilattice l1 l0 l0
FP-BJS = record
  { Carrier = Carrier-FP
  ; _≈_ = _≈_
  ; _≤_ = _≤_
  ; _∨_ = _∨'_
  ; ⊥ = ⊥'
  ; isBoundedJoinSemilattice = isBoundedJoinSemilattice-≤-∨'
  }
