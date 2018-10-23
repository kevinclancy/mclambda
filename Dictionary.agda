open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Lattice
open import Util
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List
open import Data.List.All
open import Data.List.Any as LAny
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
open import Data.Product
open import Relation.Nullary
open import Function as F using (_$_)
open import Function.Equivalence
open import Function.Equality
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.Properties.JoinSemilattice
open import Relation.Binary.Properties.BoundedJoinSemilattice
open import Level

module Dictionary (K : StrictTotalOrder l0 l0 l0) (V : BoundedJoinSemilattice l0 l0 l0) where

|K| = StrictTotalOrder.Carrier K
|V| = BoundedJoinSemilattice.Carrier V
_<_ = StrictTotalOrder._<_ K
<-trans = StrictTotalOrder.trans K
<-respˡ-≈ = StrictTotalOrder.<-respˡ-≈ K
<-irrefl = StrictTotalOrder.irrefl K
_≈k_ = StrictTotalOrder.Eq._≈_ K
≈k-sym = StrictTotalOrder.Eq.sym K
≈k-refl = StrictTotalOrder.Eq.refl K
≈k-trans = StrictTotalOrder.Eq.trans K
_≤v_ = BoundedJoinSemilattice._≤_ V
≤v-antisym = BoundedJoinSemilattice.antisym V
≤v-trans = BoundedJoinSemilattice.trans V
≤v-reflexive = BoundedJoinSemilattice.reflexive V
≤v-refl = BoundedJoinSemilattice.refl V
_≈v_ = BoundedJoinSemilattice._≈_ V
≈v-sym = BoundedJoinSemilattice.Eq.sym V
≈v-trans = BoundedJoinSemilattice.Eq.trans V
≈v-refl = BoundedJoinSemilattice.Eq.refl V
⊥v = BoundedJoinSemilattice.⊥ V
_∨v_ = BoundedJoinSemilattice._∨_ V

data IsDict : List (|K| × |V|) → Set where
  []-Dict : IsDict []
  ∷-Dict : (hd : |K| × |V|) → (tl : List (|K| × |V|)) → (All (λ · → proj₁ hd < proj₁ ·) tl) → 
              ¬ (proj₂ hd ≈v ⊥v) → (IsDict tl) → IsDict (hd ∷ tl) 

▹-Ty : Set
▹-Ty = Σ[ l ∈ (List $ |K| × |V|) ] (IsDict l) 

|E| = |K| × |V|

dict-no⊥ : (l : List |E|) → (d : IsDict l) → (e : |E|) → (e ∈≡ l) → ¬ (proj₂ e) ≈v ⊥v
dict-no⊥ [] []-Dict e e∈l = ⊥-elim $ ¬Any[] e∈l
  where
    open import Data.List.Any.Properties using (¬Any[])
dict-no⊥ (h ∷ t) (∷-Dict .h .t min ¬h≈⊥ dt) e (here PE.refl) = ¬h≈⊥
dict-no⊥ (h ∷ t) (∷-Dict .h .t min ¬h≈⊥ dt) e (there e∈t) = dict-no⊥ t dt e e∈t  

--entry comparison 
_≤e_ : |E| → |E| → Set
(k₁ , v₁) ≤e (k₂ , v₂) = (k₁ ≈k k₂) × (v₁ ≤v v₂)

≤e-trans : Transitive _≤e_
≤e-trans {k1 , v1} {k2 , v2} {k3 , v3} (k1≈k2 , v1≤v2) (k2≈k3 , v2≤v3)  = 
  (StrictTotalOrder.Eq.trans K k1≈k2 k2≈k3) , (BoundedJoinSemilattice.trans V v1≤v2 v2≤v3)

≤e-reflexive : {e1 e2 : |E|} → e1 ≡ e2 → e1 ≤e e2
≤e-reflexive PE.refl = (StrictTotalOrder.Eq.refl K , BoundedJoinSemilattice.refl V)  

_≈e_ : |E| → |E| → Set
(k1 , v1) ≈e (k2 , v2) = (k1 ≈k k2) × (v1 ≈v v2)

▹-semilat : BoundedJoinSemilattice l0 l0 l0
▹-semilat = record
  { Carrier = ▹-Ty
  ; _≈_ = _≈'_
  ; _≤_ = _≤'_
  ; _∨_ = _∨'_
  ; ⊥ = ⊥'
  ; isBoundedJoinSemilattice = record
    { isJoinSemilattice = record 
      { isPartialOrder = {!!}
      ; supremum = {!!}
      } 
    ; minimum = minimum'
    }
  }
  where
    open import Function.Equivalence
    open import Data.List.Any renaming (map to mapAny)
    open import Data.List.Any.Properties using (¬Any[])
    open import Data.List.All as LAll
    open import Data.List.Membership.Propositional
    open import Data.Empty
    open import Data.Sum
    open import Relation.Binary renaming (_⇒_ to _Implies_)
    open StrictTotalOrder K using (compare)

    Carrier' : Set
    Carrier' = ▹-Ty

    trans-≤e : Transitive _≤e_
    trans-≤e (k1≈k2 , v1≤v2) (k2≈k3 , v2≤v3) = 
      StrictTotalOrder.Eq.trans K k1≈k2 k2≈k3 , BoundedJoinSemilattice.trans V v1≤v2 v2≤v3

    _≤'_ : Carrier' → Carrier' → Set
    (l₁ , _) ≤' (l₂ , _) = All (λ e₁ → Any (λ e₂ → e₁ ≤e e₂) l₂) l₁

    -- note that this is an unusual notion of ∈, in that we require the value to be *less than* some value with matching key in the list, rather than *equal to*
    _∈'_ : |E| → Carrier' → Set
    (k , v) ∈' (l , _) = (Any ((k , v) ≤e_) l) ⊎ (v ≈v ⊥v) 

    _∈k_ : |K| → Carrier' → Set
    k ∈k (l , _) = Any (λ · → k ≈k proj₁ ·) l

    _≈'_ : Carrier' → Carrier' → Set
    i ≈' j = (i ≤' j) × (j ≤' i)

    ⊥' : Carrier'
    ⊥' = [] , []-Dict

    minimum' : (c : Carrier') → ⊥' ≤' c
    minimum' c = []

    ----- _∨'_ auxiliary functions
    --[[[
    _∨_ : List |E| → List |E| → List |E|
    --[[[
    [] ∨ [] = []
    [] ∨ (hb ∷ tb) = hb ∷ tb
    (ha ∷ ta) ∨ [] = ha ∷ ta
    (ha ∷ ta) ∨ (hb ∷ tb) with compare (proj₁ ha) (proj₁ hb) 
    (ha ∷ ta) ∨ (hb ∷ tb) | tri< ka<kb _ _ = ha ∷ (ta ∨ (hb ∷ tb))
    (ha ∷ ta) ∨ (hb ∷ tb) | tri≈ _ ka≈kb _ = (proj₁ ha , (proj₂ ha) ∨v (proj₂ hb)) ∷ (ta ∨ tb)
    (ha ∷ ta) ∨ (hb ∷ tb) | tri> _ _ kb<ka = hb ∷ ((ha ∷ ta) ∨ tb)
    --]]]

    ∨-Allk : {ℓ : Level} → {P : |K| → Set ℓ} → (l1 l2 : List |E|) → (All (λ · → P $ proj₁ ·) l1) → (All (λ · → P $ proj₁ ·) l2) → (All (λ · → P $ proj₁ ·) (l1 ∨ l2))
    --[[[
    ∨-Allk [] [] [] [] = []
    ∨-Allk [] (hb ∷ tb) [] all2 = all2
    ∨-Allk (ha ∷ ta) [] all1 [] = all1
    ∨-Allk (ha ∷ ta) (hb ∷ tb) (haP ∷ taP) (hbP ∷ tbP) with compare (proj₁ ha) (proj₁ hb) 
    ∨-Allk (ha ∷ ta) (hb ∷ tb) (haP ∷ taP) (hbP ∷ tbP) | tri< ka<kb _ _ = 
      haP ∷ ∨-Allk ta (hb ∷ tb) taP (hbP ∷ tbP)
    ∨-Allk (ha ∷ ta) (hb ∷ tb) (haP ∷ taP) (hbP ∷ tbP) | tri≈ _ ka≈kb _ = 
      haP ∷ ∨-Allk ta tb taP tbP
    ∨-Allk (ha ∷ ta) (hb ∷ tb) (haP ∷ taP) (hbP ∷ tbP) | tri> _ _ kb<ka = 
      hbP ∷ ∨-Allk (ha ∷ ta) tb (haP ∷ taP) tbP
    --]]]

    ∨-Dict : {l1 l2 : List |E|} → (f1 : IsDict l1) → (f2 : IsDict l2) → IsDict (l1 ∨ l2)
    --[[[
    ∨-Dict {[]} {[]} []-Dict []-Dict = []-Dict
    ∨-Dict {[]} {hb ∷ tb} []-Dict d2 = d2
    ∨-Dict {ha ∷ ta} {[]} d1 d2 = d1
    ∨-Dict {ha ∷ ta} {hb ∷ tb} (∷-Dict ha ta mina ¬ha≈⊥v dta) (∷-Dict hb tb minb ¬hb≈⊥v dtb) with compare (proj₁ ha) (proj₁ hb)
    ∨-Dict {ha ∷ ta} {hb ∷ tb} (∷-Dict ha ta mina ¬ha≈⊥v dta) db@(∷-Dict hb tb minb ¬hb≈⊥v dtb) | tri< ka<kb _ _ =
      ∷-Dict ha (ta ∨ (hb ∷ tb)) min' ¬ha≈⊥v (∨-Dict dta db)
      where
        min-ha-b : All (λ · → proj₁ ha < proj₁ ·) (hb ∷ tb)
        min-ha-b = ka<kb ∷ LAll.tabulate tab
          where
            tab : {x : |E|} → x ∈ tb → proj₁ ha < proj₁ x
            tab {x} x∈tb = <-trans ka<kb (LAll.lookup minb x∈tb)

        min' : All (λ · → proj₁ ha < proj₁ ·) (ta ∨ (hb ∷ tb))
        min' = ∨-Allk ta (hb ∷ tb) mina min-ha-b
    ∨-Dict {ha ∷ ta} {hb ∷ tb} (∷-Dict ha ta mina ¬ha≈⊥v dta) db@(∷-Dict hb tb minb ¬hb≈⊥v dtb) | tri≈ _ ka≈kb _ =
      ∷-Dict (proj₁ ha , (proj₂ ha) ∨v (proj₂ hb)) (ta ∨ tb) min' ¬ha∨hb≈⊥v (∨-Dict dta dtb)
      where
        min-ha-b : All (λ · → proj₁ ha < proj₁ ·) tb
        min-ha-b = LAll.tabulate tab
          where
            tab : {x : |E|} → x ∈ tb → proj₁ ha < proj₁ x
            tab {x} x∈tb = <-respˡ-≈ (≈k-sym ka≈kb) (LAll.lookup minb x∈tb)

        min' : All (λ · → proj₁ ha < proj₁ ·) (ta ∨ tb)
        min' = ∨-Allk ta tb mina min-ha-b
      
        ¬ha∨hb≈⊥v : ¬ ((proj₂ ha) ∨v (proj₂ hb)) ≈v ⊥v
        ¬ha∨hb≈⊥v ha∨hb≈⊥v = ¬ha≈⊥v $ ≤v-antisym ha≤⊥v ⊥v≤ha
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)

            ha≤⊥v : (proj₂ ha) ≤v ⊥v
            ha≤⊥v = 
              begin
                (proj₂ ha) 
                  ≤⟨ proj₁ $ BoundedJoinSemilattice.supremum V (proj₂ ha) (proj₂ hb) ⟩
                (proj₂ ha) ∨v (proj₂ hb)
                  ≈⟨ ha∨hb≈⊥v ⟩ 
                ⊥v
               ∎

            ⊥v≤ha : ⊥v ≤v (proj₂ ha)
            ⊥v≤ha = BoundedJoinSemilattice.minimum V (proj₂ ha)
    ∨-Dict {ha ∷ ta} {hb ∷ tb} da@(∷-Dict ha ta mina ¬ha≈⊥v dta) db@(∷-Dict hb tb minb ¬hb≈⊥v dtb) | tri> _ _ kb<ka =
      ∷-Dict hb ((ha ∷ ta) ∨ tb) min' ¬hb≈⊥v (∨-Dict da dtb)
      where
        min-hb-a : All (λ · → proj₁ hb < proj₁ ·) (ha ∷ ta)
        min-hb-a = kb<ka ∷ LAll.tabulate tab
          where
            tab : {x : |E|} → x ∈ ta → proj₁ hb < proj₁ x
            tab {x} x∈ta = <-trans kb<ka (LAll.lookup mina x∈ta)

        min' : All (λ · → proj₁ hb < proj₁ ·) ((ha ∷ ta) ∨ tb)
        min' = ∨-Allk (ha ∷ ta) tb min-hb-a minb         
    --]]]
    --]]] 

    _∨'_ : Carrier' → Carrier' → Carrier'
    (la , da) ∨' (lb , db) = (la ∨ lb , ∨-Dict da db)
    
    ----- Proof that _∨'_ is a supremum
    --[[[

    k-union : (a b : Carrier') → (k : |K|) → (k ∈k a) ⊎ (k ∈k b) → k ∈k (a ∨' b)
    k-union ([] , da) ([] , db) k (inj₁ k∈[]) = ⊥-elim $ ¬Any[] k∈[]
    k-union ([] , da) ([] , db) k (inj₂ k∈[]) = ⊥-elim $ ¬Any[] k∈[]
    k-union ([] , da) (hb ∷ tb , db) k (inj₁ k∈[]) = ⊥-elim $ ¬Any[] k∈[]
    k-union ([] , da) (hb ∷ tb , db) k (inj₂ k∈b) = {!!}
    k-union (x ∷ la , da) (lb , db) k = {!!}

    P∨ : (a b : Carrier') → (e : |E|) → Set
    P∨ a b (k , v) = Σ[ va ∈ |V| ] Σ[ vb ∈ |V| ] ((k , va) ∈' a) × ((k , vb) ∈' b) × (v ≤v (va ∨v vb))   
    
    e∈a∨b→P∨ : (a : List |E|) → (da : IsDict a) → (b : List |E|) → (db : IsDict b) → (e : |E|) → 
                   (e ∈' ((a , da) ∨' (b , db))) → (P∨ (a , da) (b , db) e)
    --[[[
    e∈a∨b→P∨ _ _ _ _ _ (inj₂ v≈⊥) = 
      (⊥v , ⊥v , inj₂ ≈v-refl , inj₂ ≈v-refl , ≤-respˡ-≈ (≈v-sym v≈⊥) ⊥≤⊥∨⊥)
      where
        open BoundedJoinSemilattice V
        ⊥≤⊥∨⊥ : ⊥v ≤v (⊥v ∨v ⊥v)
        ⊥≤⊥∨⊥ = minimum (⊥v ∨v ⊥v)

    e∈a∨b→P∨ [] []-Dict [] []-Dict e@(k , v) (inj₁ ())
    e∈a∨b→P∨ la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) [] []-Dict e@(k , v) (inj₁ e≤a) = 
      anyEliminate (proj₁ a) elim e≤a
      where
        a = ((kha , vha) ∷ ta) , (∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta)
        b = [] , []-Dict

        elim : AnyEliminator {ℓQ = l0} |E| (P∨ a b e) ((k , v) ≤e_) (proj₁ a)
        elim (kz , vz) f (k≈kz , v≤vz) z∈≡a = vz , ⊥v , inj₁ kvz≤a , inj₂ ≈v-refl , ≤v-trans v≤vz vz≤vz∨⊥
          where
            open import Relation.Binary.Properties.BoundedJoinSemilattice

            vz≤vz∨⊥ : vz ≤v (vz ∨v ⊥v)
            vz≤vz∨⊥ = ≤v-reflexive $ ≈v-sym $ identityʳ V vz

            kvz≤a : Any ((k , vz) ≤e_) la
            kvz≤a = LAny.map aux z∈≡a
              where
                aux : {x : |E|} → (kz , vz) ≡ x → (k , vz) ≤e x
                aux {kx , vx} PE.refl = (k≈kz , ≤v-refl) 

    e∈a∨b→P∨ [] []-Dict lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (inj₁ e≤b) = 
      anyEliminate (proj₁ b) elim e≤b
      where
        a = [] , []-Dict
        b = ((khb , vhb) ∷ tb) , (∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb)

        elim : AnyEliminator {ℓQ = l0} |E| (P∨ a b e) ((k , v) ≤e_) (proj₁ b)
        elim (kz , vz) f (k≈kz , v≤vz) z∈≡b = ⊥v , vz , inj₂ ≈v-refl , inj₁ kvz≤b , ≤v-trans v≤vz vz≤vz∨⊥
          where
            open import Relation.Binary.Properties.BoundedJoinSemilattice

            vz≤vz∨⊥ : vz ≤v (⊥v ∨v vz)
            vz≤vz∨⊥ = ≤v-reflexive $ ≈v-sym $ identityˡ V vz

            kvz≤b : Any ((k , vz) ≤e_) lb
            kvz≤b = LAny.map aux z∈≡b
              where
                aux : {x : |E|} → (kz , vz) ≡ x → (k , vz) ≤e x
                aux {kx , vx} PE.refl = (k≈kz , ≤v-refl)
    e∈a∨b→P∨ la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (inj₁ e≤b) with compare kha khb
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (inj₁ (here (k≈ka , v≤va))) | tri< kha<khb _ _ = 
      vha , ⊥v , inj₁ (here $ k≈ka , ≤v-refl) , inj₂ ≈v-refl , ≤v-trans v≤va vha≤vha∨⊥
      where
        open import Relation.Binary.Properties.BoundedJoinSemilattice
        open BoundedJoinSemilattice V

        vha≤vha∨⊥ : vha ≤v (vha ∨v ⊥v)
        vha≤vha∨⊥ = ≤v-reflexive $ ≈v-sym $ identityʳ V vha
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (inj₁ (there e∈ta∨b)) | tri< kha<khb _ _
      with  e∈a∨b→P∨ ta dta lb db e (inj₁ e∈ta∨b)
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (inj₁ (there e∈ta∨b)) | tri< kha<khb _ _ | va , vb , inj₁ va≤ta , vb∈b , v≤va∨vb =
      va , vb , inj₁ (there va≤ta) , vb∈b  , v≤va∨vb
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (inj₁ (there e∈ta∨b)) | tri< kha<khb _ _ | va , vb , inj₂ va≈⊥ , vb∈b , v≤va∨vb =
      va , vb , inj₂ va≈⊥ , vb∈b  , v≤va∨vb
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (inj₁ (here (k≈kha , v≤vha∨vhb))) | tri≈ _ kha≈khb _ = 
      vha , vhb , (inj₁ $ here (k≈kha , ≤v-refl)) , (inj₁ $ here (≈k-trans k≈kha kha≈khb , ≤v-refl)) , v≤vha∨vhb
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (inj₁ (there e∈ta∨tb)) | tri≈ _ kha≈khb _ 
      with e∈a∨b→P∨ ta dta tb dtb e (inj₁ e∈ta∨tb)
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (inj₁ (there e∈ta∨tb)) | tri≈ _ kha≈khb _ | va , vb , inj₁ va≤ta , inj₁ vb≤tb , v≤va∨vb = 
      va , vb , inj₁ (there va≤ta) , inj₁ (there vb≤tb) , v≤va∨vb
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (inj₁ (there e∈ta∨tb)) | tri≈ _ kha≈khb _ | va , vb , inj₁ va≤ta , inj₂ vb≈⊥ , v≤va∨vb = 
      va , ⊥v , inj₁ (there va≤ta) , inj₂ ≈v-refl , ≤v-trans v≤va∨vb (≤v-reflexive $ ∨-cong joinSemiLattice ≈v-refl vb≈⊥)
      where
        open BoundedJoinSemilattice V
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (inj₁ (there e∈ta∨tb)) | tri≈ _ kha≈khb _ | va , vb , inj₂ va≈⊥ , inj₁ vb≤tb , v≤va∨vb = 
      ⊥v , vb , inj₂ ≈v-refl , inj₁ (there vb≤tb) , ≤v-trans v≤va∨vb (≤v-reflexive $ ∨-cong joinSemiLattice va≈⊥ ≈v-refl) 
      where
        open BoundedJoinSemilattice V
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (inj₁ (there e∈ta∨tb)) | tri≈ _ kha≈khb _ | va , vb , inj₂ va≈⊥ , inj₂ vb≈⊥ , v≤va∨vb = 
      ⊥v , ⊥v , inj₂ ≈v-refl , inj₂ ≈v-refl , ≤v-trans v≤va∨vb (≤v-reflexive $ ∨-cong joinSemiLattice va≈⊥ vb≈⊥)
      where
        open BoundedJoinSemilattice V
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (inj₁ (here (k≈khb , v≤vb))) | tri> _ _ khb<kha = 
      ⊥v , vhb , inj₂ ≈v-refl , inj₁ (here $ k≈khb , ≤v-refl) , ≤v-trans v≤vb vhb≤⊥∨vhb
      where
        open import Relation.Binary.Properties.BoundedJoinSemilattice
        open import Relation.Binary.Properties.JoinSemilattice
        open BoundedJoinSemilattice V

        vhb≤⊥∨vhb : vhb ≤v (⊥v ∨v vhb)
        vhb≤⊥∨vhb = ≤v-reflexive $ ≈v-sym $ identityˡ V vhb
    e∈a∨b→P∨ la@((kha , vha) ∷ ta) da@(∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (inj₁ (there e∈ta∨b)) | tri> kha<khb _ _ with e∈a∨b→P∨ la da tb dtb e (inj₁ e∈ta∨b)
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (inj₁ (there e∈ta∨b)) | tri> kha<khb _ _ | va , vb , va∈a , inj₁ vb≤tb , v≤va∨vb = 
      va , vb , va∈a , inj₁ (there vb≤tb) , v≤va∨vb
    e∈a∨b→P∨ ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (inj₁ (there e∈ta∨b)) | tri> kha<khb _ _ | va , vb , va∈a , inj₂ vb≈⊥ , v≤va∨vb = 
      va , vb , va∈a , inj₂ vb≈⊥  , v≤va∨vb
    --]]]

    P∨→e∈a∨b : (a : List |E|) → (da : IsDict a) → (b : List |E|) → (db : IsDict b) → (e : |E|) → 
               (P∨ (a , da) (b , db) e) → (e ∈' ((a , da) ∨' (b , db)))
    --[[[
    P∨→e∈a∨b [] []-Dict [] []-Dict e@(k , v) (va , vb , inj₁ () , kvb∈b , v≤va∨vb)
    P∨→e∈a∨b [] []-Dict [] []-Dict e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ () , v≤va∨vb)
    P∨→e∈a∨b [] []-Dict [] []-Dict e@(k , v) (va , vb , inj₂ va≈⊥ , inj₂ vb≈⊥ , v≤va∨vb) = inj₂ (≤v-antisym v≤⊥ (minimum v))
      where
        open BoundedJoinSemilattice V
        open import Relation.Binary.Properties.BoundedJoinSemilattice
        open import Relation.Binary.Properties.JoinSemilattice

        ⊥∨⊥≈⊥ : ⊥v ∨v ⊥v ≈ ⊥v
        ⊥∨⊥≈⊥ = identityˡ V ⊥v

        va∨vb≈⊥∨⊥ : (va ∨v vb) ≈v (⊥v ∨v ⊥v)
        va∨vb≈⊥∨⊥ = ∨-cong joinSemiLattice va≈⊥ vb≈⊥ 

        v≤⊥ : v ≤v ⊥v
        v≤⊥ = ≤v-trans v≤va∨vb (≤v-reflexive (≈v-trans va∨vb≈⊥∨⊥ ⊥∨⊥≈⊥))
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) [] []-Dict e@(k , v) (va , vb , kva∈a , inj₁ () , v≤va∨vb)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) [] []-Dict e@(k , v) (va , vb , inj₁ kva≤a , inj₂ vb≈⊥ , v≤va∨vb) =
      inj₁ (LAny.map (≤e-trans (≈k-refl , v≤va)) kva≤a)
      where
        open import Relation.Binary.Properties.BoundedJoinSemilattice
        open import Relation.Binary.Properties.JoinSemilattice
        open BoundedJoinSemilattice V

        v≤va : v ≤v va 
        v≤va =
          begin
            v ≤⟨ v≤va∨vb ⟩
            (va ∨v vb) ≈⟨ ∨-cong joinSemiLattice ≈v-refl vb≈⊥ ⟩
            (va ∨v ⊥v) ≈⟨ identityʳ V va ⟩
            va
           ∎
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) [] []-Dict e@(k , v) (va , vb , inj₂ va≈⊥ , inj₂ vb≈⊥ , v≤va∨vb) = 
      inj₂ (≤v-antisym v≤⊥ (minimum v))
      where
        open import Relation.Binary.Properties.BoundedJoinSemilattice
        open import Relation.Binary.Properties.JoinSemilattice
        open BoundedJoinSemilattice V

        va∨vb≈⊥ : (va ∨v vb) ≈v ⊥v
        va∨vb≈⊥ = ≈v-trans (∨-cong joinSemiLattice va≈⊥ vb≈⊥) (identityˡ V ⊥v)

        v≤⊥ : v ≤v ⊥v
        v≤⊥ = ≤v-trans v≤va∨vb (≤v-reflexive va∨vb≈⊥)
    P∨→e∈a∨b [] []-Dict lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ () , _  , _)
    P∨→e∈a∨b [] []-Dict lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ kvb≤b , v≤va∨vb) =
      inj₁ (LAny.map (≤e-trans (≈k-refl , v≤vb)) kvb≤b)
      where
        open import Relation.Binary.Properties.BoundedJoinSemilattice
        open import Relation.Binary.Properties.JoinSemilattice
        open BoundedJoinSemilattice V

        v≤vb : v ≤v vb
        v≤vb =
          begin
            v ≤⟨ v≤va∨vb ⟩
            (va ∨v vb) ≈⟨ ∨-cong joinSemiLattice va≈⊥ ≈v-refl ⟩
            (⊥v ∨v vb) ≈⟨ identityˡ V vb ⟩
            vb
           ∎
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)
    P∨→e∈a∨b [] []-Dict lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₂ vb≈⊥ , v≤va∨vb) = 
      inj₂ (≤v-antisym v≤⊥ (minimum v))
      where
        open import Relation.Binary.Properties.BoundedJoinSemilattice
        open import Relation.Binary.Properties.JoinSemilattice
        open BoundedJoinSemilattice V

        va∨vb≈⊥ : (va ∨v vb) ≈v ⊥v
        va∨vb≈⊥ = ≈v-trans (∨-cong joinSemiLattice va≈⊥ vb≈⊥) (identityˡ V ⊥v)

        v≤⊥ : v ≤v ⊥v
        v≤⊥ = ≤v-trans v≤va∨vb (≤v-reflexive va∨vb≈⊥)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) P∨abe with compare kha khb
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ (here (k≈kha , _)) , inj₁ (here (k≈khb , _)) , v≤va∨vb) | tri< kha<khb _ _ = 
      ⊥-elim $ <-irrefl (≈k-trans (≈k-sym k≈kha) k≈khb) kha<khb
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ (here (k≈kha , v≤vha)) , inj₁ (there vb≤tb) , v≤va∨vb) | tri< kha<khb _ _ = 
       ⊥-elim $ anyEliminate tb elim vb≤tb 
       where
         elim : AnyEliminator {ℓQ = l0} |E| ⊥ ((k , vb) ≤e_) tb
         elim (kz , vz) f (k≈kz , vb≤vz) z∈≡tb = ⊥-elim $ <-irrefl (≈k-trans (≈k-sym k≈kha) k≈kz) (<-trans kha<khb (LAll.lookup minb z∈≡tb))
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ (there va≤ta) , inj₁ vb≤b , v≤va∨vb) | tri< kha<khb _ _ 
      with P∨→e∈a∨b ta dta lb db e (va , vb , inj₁ va≤ta , inj₁ vb≤b , v≤va∨vb)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ (there va≤ta) , inj₁ vb≤b , v≤va∨vb) | tri< kha<khb _ _ | inj₁ e≤ta∨b = 
      inj₁ (there e≤ta∨b)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ (there va≤ta) , inj₁ vb≤b , v≤va∨vb) | tri< kha<khb _ _ | inj₂ v≈⊥ = 
      inj₂ v≈⊥
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₂ vb≈⊥ , v≤va∨vb) | tri< kha<khb _ _ with kv≤a
      where
        open BoundedJoinSemilattice V

        v≤va : v ≤v va
        v≤va = 
          begin
            v ≤⟨ v≤va∨vb ⟩
            va ∨v vb ≈⟨ ∨-cong joinSemiLattice ≈v-refl vb≈⊥ ⟩
            va ∨v ⊥v ≈⟨ identityʳ V va ⟩
            va
           ∎
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)

        kv≤a : Any (e ≤e_) la
        kv≤a = LAny.map aux va≤a
          where
            aux : {x : |E|} → (k , va) ≤e x → (k , v) ≤e x
            aux {kx , vx} (k≈kx , va≤vx) = k≈kx , ≤v-trans v≤va va≤vx
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₂ vb≈⊥ , v≤va∨vb) | tri< kha<khb _ _ | here kv≤h = 
      inj₁ $ here kv≤h
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₂ vb≈⊥ , v≤va∨vb) | tri< kha<khb _ _ | there kv≤ta 
      with P∨→e∈a∨b ta dta lb db e (v , ⊥v , inj₁ kv≤ta , inj₂ ≈v-refl , ≤v-reflexive (≈v-sym $ identityʳ V v)) 
      where
        open BoundedJoinSemilattice V
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₂ vb≈⊥ , v≤va∨vb) | tri< kha<khb _ _ | there kv≤ta | inj₁ kv≤t = 
      inj₁ (there kv≤t)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₂ vb≈⊥ , v≤va∨vb) | tri< kha<khb _ _ | there kv≤ta | inj₂ v≈⊥ = 
      inj₂ v≈⊥
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ vb≤b , v≤va∨vb) | tri< kha<khb _ _
      with P∨→e∈a∨b ta dta lb db e (⊥v , vb , inj₂ ≈v-refl , inj₁ vb≤b , v≤⊥∨vb)
      where
        open BoundedJoinSemilattice V

        v≤⊥∨vb : v ≤v (⊥v ∨v vb)
        v≤⊥∨vb = 
          begin
            v ≤⟨ v≤va∨vb ⟩
            va ∨v vb ≈⟨ ∨-cong joinSemiLattice va≈⊥ ≈v-refl ⟩
            ⊥v ∨v vb
           ∎ 
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)      
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ vb≤b , v≤va∨vb) | tri< kha<khb _ _ | inj₁ x≤ta∨b = 
      inj₁ (there x≤ta∨b)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ vb≤b , v≤va∨vb) | tri< kha<khb _ _ | inj₂ v≈⊥ = 
      inj₂ v≈⊥
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₂ vb≈⊥ , v≤va∨vb) | tri< kha<khb _ _ =
      inj₂ v≈⊥
      where
        open BoundedJoinSemilattice V

        v≤⊥ : v ≤v ⊥v
        v≤⊥ = 
          begin
            v ≤⟨ v≤va∨vb ⟩
            va ∨v vb ≈⟨ ∨-cong joinSemiLattice va≈⊥ vb≈⊥  ⟩
            ⊥v ∨v ⊥v ≈⟨ identityˡ V ⊥v ⟩ 
            ⊥v
           ∎
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)

        v≈⊥ : v ≈v ⊥v
        v≈⊥ = ≤v-antisym v≤⊥ (minimum v)

    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₁ (here (k≈kha , va≤vha)) , inj₁ (here (k≈khb , vb≤vhb)) , v≤va∨vb) | tri≈ _ kha≈khb _ = 
      inj₁ $ here (k≈kha , v≤vha∨vhb)
      where
        v≤vha∨vhb : v ≤v (vha ∨v vhb)
        v≤vha∨vhb = 
          begin
            v ≤⟨ v≤va∨vb ⟩
            (va ∨v vb) ≤⟨ ∨-monotonic joinSemiLattice va≤vha vb≤vhb ⟩
            (vha ∨v vhb)
           ∎
          where
            open BoundedJoinSemilattice V
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₁ (here (k≈kha , va≤vha)) , inj₁ (there vb≤tb) , v≤va∨vb) | tri≈ _ kha≈khb _ = 
      ⊥-elim $ anyEliminate tb elim vb≤tb
      where
        elim : AnyEliminator {ℓQ = l0} |E| ⊥ ((k , vb) ≤e_) tb
        elim (kz , vz) f (k≈kz , vb≤vz) z∈≡tb = <-irrefl k≈kz k<kz
          where
            k<kz : k < kz
            k<kz = <-respˡ-≈ (≈k-trans (≈k-sym kha≈khb) (≈k-sym k≈kha)) (LAll.lookup minb z∈≡tb)
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₁ (there va≤ta) , inj₁ (here (k≈khb , vb≤vhb)) , v≤va∨vb) | tri≈ _ kha≈khb _ = 
      ⊥-elim $ anyEliminate ta elim va≤ta
      where
        elim : AnyEliminator {ℓQ = l0} |E| ⊥ ((k , va) ≤e_) ta
        elim (kz , vz) f (k≈kz , va≤vz) z∈≡ta = <-irrefl k≈kz k<kz
          where
            k<kz : k < kz
            k<kz = <-respˡ-≈ (≈k-trans kha≈khb (≈k-sym k≈khb)) (LAll.lookup mina z∈≡ta)
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ (there va≤ta) , inj₁ (there vb≤tb) , v≤va∨vb) | tri≈ _ kha≈khb _ 
      with P∨→e∈a∨b ta dta tb dtb e (va , vb , inj₁ va≤ta , inj₁ vb≤tb , v≤va∨vb)
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₁ (there va≤ta) , inj₁ (there vb≤tb) , v≤va∨vb) | tri≈ _ kha≈khb _ | inj₁ e≤ta∨tb =
      inj₁ $ there e≤ta∨tb
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₁ (there va≤ta) , inj₁ (there vb≤tb) , v≤va∨vb) | tri≈ _ kha≈khb _ | inj₂ v≈⊥ =
      inj₂ v≈⊥ 
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₁ va≤a , inj₂ vb≈⊥ , v≤va∨vb) | tri≈ _ kha≈khb _ with v≤va 
      where
        open BoundedJoinSemilattice V
        v≤va : v ≤v va 
        v≤va =
          begin
            v ≤⟨ v≤va∨vb ⟩
            (va ∨v vb) ≈⟨ ∨-cong joinSemiLattice ≈v-refl vb≈⊥ ⟩
            (va ∨v ⊥v) ≈⟨ identityʳ V va ⟩
            va
           ∎
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₁ (here (k≈kha , va≤vha)) , inj₂ vb≈⊥ , v≤va∨vb) | tri≈ _ kha≈khb _ | v≤va =
      inj₁ $ here (k≈kha , v≤vha∨vhb) 
      where
        v≤vha∨vhb : v ≤v (vha ∨v vhb)
        v≤vha∨vhb = 
          begin
            v ≤⟨ v≤va ⟩ 
            va ≤⟨ va≤vha ⟩
            vha ≤⟨ proj₁ $ BoundedJoinSemilattice.supremum V vha vhb ⟩
            (vha ∨v vhb)
           ∎ 
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ (there va≤ta) , inj₂ vb≈⊥ , v≤va∨vb) | tri≈ _ kha≈khb _ | v≤va
      with P∨→e∈a∨b ta dta tb dtb e (v , ⊥v , inj₁ e≤ta , inj₂ ≈v-refl , (≤v-reflexive $ ≈v-sym $ identityʳ V v))
      where
        e≤ta : Any (e ≤e_) ta
        e≤ta = LAny.map aux va≤ta
          where
            aux : {x : |E|} → (k , va) ≤e x → (k , v) ≤e x
            aux {kx , vx} (k≈kx , va≤vx) = k≈kx , ≤v-trans v≤va va≤vx 
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₁ (there e≤ta) , inj₂ vb≈⊥ , v≤va∨vb) | tri≈ _ kha≈khb _ | v≤va | inj₁ e≤ta∨tb = 
      inj₁ $ there e≤ta∨tb
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₁ (there e≤ta) , inj₂ vb≈⊥ , v≤va∨vb) | tri≈ _ kha≈khb _ | v≤va | inj₂ v≈⊥ = 
      inj₂ v≈⊥
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₂ va≈⊥ , inj₁ vb≤b , v≤va∨vb) | tri≈ _ kha≈khb _ with v≤vb
      where
        open BoundedJoinSemilattice V
        v≤vb : v ≤v vb 
        v≤vb =
          begin
            v ≤⟨ v≤va∨vb ⟩
            (va ∨v vb) ≈⟨ ∨-cong joinSemiLattice va≈⊥ ≈v-refl ⟩
            (⊥v ∨v vb) ≈⟨ identityˡ V vb ⟩
            vb
           ∎
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₂ va≈⊥ , inj₁ (here (k≈khb , va≤vhb)) , v≤va∨vb) | tri≈ _ kha≈khb _ | v≤vb =
      inj₁ $ here ((≈k-trans k≈khb (≈k-sym kha≈khb)) , v≤vha∨vhb) 
      where
        v≤vha∨vhb : v ≤v (vha ∨v vhb)
        v≤vha∨vhb = 
          begin
            v ≤⟨ v≤vb ⟩ 
            vb ≤⟨ va≤vhb ⟩
            vhb ≤⟨ proj₁ $ proj₂ $ BoundedJoinSemilattice.supremum V vha vhb ⟩
            (vha ∨v vhb)
           ∎ 
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ (there vb≤tb) , v≤va∨vb) | tri≈ _ kha≈khb _ | v≤vb
      with P∨→e∈a∨b ta dta tb dtb e (⊥v , v , inj₂ ≈v-refl , inj₁ e≤tb , (≤v-reflexive $ ≈v-sym $ identityˡ V v))
      where
        e≤tb : Any (e ≤e_) tb
        e≤tb = LAny.map aux vb≤tb
          where
            aux : {x : |E|} → (k , vb) ≤e x → (k , v) ≤e x
            aux {kx , vx} (k≈kx , vb≤vx) = k≈kx , ≤v-trans v≤vb vb≤vx 
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₂ va≈⊥ , inj₁ (there vb≤tb) , v≤va∨vb) | tri≈ _ kha≈khb _ | v≤vb | inj₁ e≤ta∨tb = 
      inj₁ $ there e≤ta∨tb
    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₂ va≈⊥ , inj₁ (there vb≤tb) , v≤va∨vb) | tri≈ _ kha≈khb _ | v≤vb | inj₂ v≈⊥ = 
      inj₂ v≈⊥

    P∨→e∈a∨b ((kha , vha) ∷ ta) (∷-Dict .(kha , vha) ta mina ¬ha≈⊥ dta) ((khb , vhb) ∷ tb) (∷-Dict .(khb , vhb) tb minb ¬hb≈⊥ dtb) (k , v) (va , vb , inj₂ va≈⊥ , inj₂ vb≈⊥ , v≤va∨vb) | tri≈ _ khb≈kha _ = inj₂ (≤v-antisym v≤⊥ (minimum v))
      where
        open BoundedJoinSemilattice V

        ⊥∨⊥≈⊥ : ⊥v ∨v ⊥v ≈ ⊥v
        ⊥∨⊥≈⊥ = identityˡ V ⊥v

        va∨vb≈⊥∨⊥ : (va ∨v vb) ≈v (⊥v ∨v ⊥v)
        va∨vb≈⊥∨⊥ = ∨-cong joinSemiLattice va≈⊥ vb≈⊥ 

        v≤⊥ : v ≤v ⊥v
        v≤⊥ = ≤v-trans v≤va∨vb (≤v-reflexive (≈v-trans va∨vb≈⊥∨⊥ ⊥∨⊥≈⊥))
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ (here (k≈kha , v≤vha)) , inj₁ (here (k≈khb , v≤vhb)) , v≤va∨vb) | tri> _ _ khb<kha = 
      ⊥-elim $ <-irrefl (≈k-trans (≈k-sym k≈khb) k≈kha) khb<kha
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ (there va≤ta) , inj₁ (here (k≈khb , v≤vhb)) , v≤va∨vb) | tri> _ _ khb<kha = 
       ⊥-elim $ anyEliminate ta elim va≤ta 
       where
         elim : AnyEliminator {ℓQ = l0} |E| ⊥ ((k , va) ≤e_) ta
         elim (kz , vz) f (k≈kz , va≤vz) z∈≡ta = ⊥-elim $ <-irrefl (≈k-trans (≈k-sym k≈khb) k≈kz) (<-trans khb<kha (LAll.lookup mina z∈≡ta))
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₁ (there vb≤tb) , v≤va∨vb) | tri> _ _ khb<kha
      with P∨→e∈a∨b la da tb dtb e (va , vb , inj₁ va≤a , inj₁ vb≤tb , v≤va∨vb)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₁ (there vb≤tb) , v≤va∨vb) | tri> _ _ khb<kha | inj₁ e≤a∨tb = 
      inj₁ (there e≤a∨tb)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₁ (there vb≤tb) , v≤va∨vb) | tri> _ _ khb<kha | inj₂ v≈⊥ = 
      inj₂ v≈⊥
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ vb≤b , v≤va∨vb) | tri> _ _ khb<kha with kv≤b
      where
        open BoundedJoinSemilattice V

        v≤vb : v ≤v vb
        v≤vb = 
          begin
            v ≤⟨ v≤va∨vb ⟩
            va ∨v vb ≈⟨ ∨-cong joinSemiLattice va≈⊥ ≈v-refl ⟩
            ⊥v ∨v vb ≈⟨ identityˡ V vb ⟩
            vb
           ∎
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)

        kv≤b : Any (e ≤e_) lb
        kv≤b = LAny.map aux vb≤b
          where
            aux : {x : |E|} → (k , vb) ≤e x → (k , v) ≤e x
            aux {kx , vx} (k≈kx , vb≤vx) = k≈kx , ≤v-trans v≤vb vb≤vx
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ vb≤b , v≤va∨vb) | tri> _ _ khb<kha | here kv≤h = 
      inj₁ $ here kv≤h
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ vb≤b , v≤va∨vb) | tri> _ _ khb<kha | there kv≤tb 
      with P∨→e∈a∨b la da tb dtb e (⊥v , v , inj₂ ≈v-refl , inj₁ kv≤tb , ≤v-reflexive (≈v-sym $ identityˡ V v)) 
      where
        open BoundedJoinSemilattice V
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ vb≤b , v≤va∨vb) | tri> _ _ khb<kha | there kv≤ta | inj₁ kv≤t = 
      inj₁ (there kv≤t)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₁ vb≤b , v≤va∨vb) | tri> _ _ khb<kha | there kv≤ta | inj₂ v≈⊥ = 
      inj₂ v≈⊥
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₂ vb≈⊥ , v≤va∨vb) | tri> _ _ khb<kha
      with P∨→e∈a∨b la da tb dtb e (va , ⊥v , inj₁ va≤a , inj₂ ≈v-refl , v≤va∨⊥)
      where
        open BoundedJoinSemilattice V

        v≤va∨⊥ : v ≤v (va ∨v ⊥v)
        v≤va∨⊥ = 
          begin
            v ≤⟨ v≤va∨vb ⟩
            va ∨v vb ≈⟨ ∨-cong joinSemiLattice ≈v-refl vb≈⊥ ⟩
            va ∨v ⊥v
           ∎ 
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)      
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₂ vb≈⊥ , v≤va∨vb) | tri> _ _ khb<kha | inj₁ x≤a∨tb = 
      inj₁ (there x≤a∨tb)
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₁ va≤a , inj₂ vb≈⊥ , v≤va∨vb) | tri> _ _ khb<kha | inj₂ v≈⊥ = 
      inj₂ v≈⊥
    P∨→e∈a∨b la@((kha , vha) ∷ ta) da@(∷-Dict (kha , vha) ta mina ¬ha≈⊥ dta) lb@((khb , vhb) ∷ tb) db@(∷-Dict (khb , vhb) tb minb ¬hb≈⊥ dtb) e@(k , v) (va , vb , inj₂ va≈⊥ , inj₂ vb≈⊥ , v≤va∨vb) | tri> _ _ khb<kha =
      inj₂ v≈⊥
      where
        open BoundedJoinSemilattice V

        v≤⊥ : v ≤v ⊥v
        v≤⊥ = 
          begin
            v ≤⟨ v≤va∨vb ⟩
            va ∨v vb ≈⟨ ∨-cong joinSemiLattice va≈⊥ vb≈⊥  ⟩
            ⊥v ∨v ⊥v ≈⟨ identityˡ V ⊥v ⟩ 
            ⊥v
           ∎
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset V)

        v≈⊥ : v ≈v ⊥v
        v≈⊥ = ≤v-antisym v≤⊥ (minimum v)
    --]]]

    e∈a∨b⇔P∨ : (a b : Carrier') → (e : |E|) → (e ∈' (a ∨' b)) ⇔ (P∨ a b e)
    e∈a∨b⇔P∨ (la , da) (lb , db) e = equivalence (e∈a∨b→P∨ la da lb db e) (P∨→e∈a∨b la da lb db e)

    ∨-monoˡ : (a b c : Carrier') → a ≤' b → (a ∨' c) ≤' (b ∨' c)
    ∨-monoˡ a@(la , da) b@(lb , db) c@(lc , dc) a≤b = LAll.tabulate tab'
      where
        tab : {kv : |E|} → kv ∈ (proj₁ $ a ∨' c) → kv ∈' (b ∨' c)
        --[[[
        tab {kv@(k , v)} kv∈a∨c with to ⟨$⟩ (inj₁ $ LAny.map aux kv∈a∨c) 
          where
            open Equivalence (e∈a∨b⇔P∨ a c kv)
            aux : {x : |E|} → kv ≡ x → kv ≤e x
            aux {x} PE.refl = (≈k-refl , ≤v-refl)
        tab {kv@(k , v)} kv∈a∨c | va , vc , inj₁ kva≤a , kvc∈c , v≤va∨vc = 
          anyEliminate la elim kva≤a 
          where
            elim : AnyEliminator {ℓQ = l0} |E| (kv ∈' (b ∨' c)) ((k , va) ≤e_) la
            elim z@(kz , vz) f (k≈kz , va≤vz) z∈≡la with LAll.lookup a≤b z∈≡la
            elim z@(kz , vz) f (k≈kz , va≤vz) z∈≡la | z≤b = anyEliminate lb elim' z≤b
              where
                elim' : AnyEliminator {ℓQ = l0} |E| (kv ∈' (b ∨' c)) (z ≤e_) lb
                elim' w@(kw , vw) f (kz≈kw , vz≤vw) w∈≡lb = 
                  from ⟨$⟩ (vw , vc , (inj₁ $ LAny.map aux w∈≡lb) , kvc∈c , v≤vw∨vc)
                  where
                    open Equivalence (e∈a∨b⇔P∨ b c kv)
                    open BoundedJoinSemilattice V 
                    open import Relation.Binary.Properties.JoinSemilattice
                   
                    k≈kw : k ≈k kw
                    k≈kw = ≈k-trans k≈kz kz≈kw
                    
                    va≤vw : va ≤v vw
                    va≤vw = ≤v-trans va≤vz vz≤vw

                    v≤vw∨vc : v ≤v (vw ∨v vc)
                    v≤vw∨vc = ≤v-trans v≤va∨vc (∨-monotonic joinSemiLattice va≤vw ≤v-refl)
                  
                    aux : {x : |E|} → (kw , vw) ≡ x → (k , vw) ≤e x
                    aux {x} PE.refl = k≈kw , ≤v-refl
        tab {kv@(k , v)} kv∈a∨c | va , vc , inj₂ va≈⊥ , kvc∈c , v≤va∨vc = 
          from ⟨$⟩ (⊥v , vc , inj₂ ≈v-refl , kvc∈c , ≤-respʳ-≈ (∨-cong joinSemiLattice va≈⊥ ≈v-refl) v≤va∨vc ) 
          where
            open Equivalence (e∈a∨b⇔P∨ b c kv)          
            open BoundedJoinSemilattice V 
            open import Relation.Binary.Properties.JoinSemilattice
        --]]]

        p : All (λ z → z ∈' (b ∨' c)) (proj₁ $ (a ∨' c))
        p = LAll.tabulate tab

        tab' : {kv : |E|} → kv ∈ (proj₁ $ (a ∨' c)) → Any (kv ≤e_) (proj₁ $ b ∨' c)
        --[[[
        tab' {k , v} kv∈a∨c with LAll.lookup p kv∈a∨c
        tab' {k , v} kv∈a∨c | inj₁ kv≤b∨c = kv≤b∨c
        tab' {k , v} kv∈a∨c | inj₂ v≈⊥ = ⊥-elim $ ¬v≈⊥ v≈⊥ 
          where
            ¬v≈⊥ : ¬ (v ≈v ⊥v) 
            ¬v≈⊥ = dict-no⊥ (proj₁ $ a ∨' c) (∨-Dict da dc) (k , v) kv∈a∨c
        --]]]

    ∨-monoʳ : (a b c : Carrier') → b ≤' c → (a ∨' b) ≤' (a ∨' c)
    --[[[
    ∨-monoʳ a@(la , da) b@(lb , db) c@(lc , dc) b≤c = LAll.tabulate tab'
      where
        tab : {kv : |E|} → kv ∈ (proj₁ $ a ∨' b) → kv ∈' (a ∨' c)
        --[[[
        tab {kv@(k , v)} kv∈a∨b with to ⟨$⟩ (inj₁ $ LAny.map aux kv∈a∨b) 
          where
            open Equivalence (e∈a∨b⇔P∨ a b kv)
            aux : {x : |E|} → kv ≡ x → kv ≤e x
            aux {x} PE.refl = (≈k-refl , ≤v-refl)
        tab {kv@(k , v)} kv∈a∨b | va , vb , kva∈a , inj₁ kvb≤b , v≤va∨vb = 
          anyEliminate lb elim kvb≤b 
          where
            elim : AnyEliminator {ℓQ = l0} |E| (kv ∈' (a ∨' c)) ((k , vb) ≤e_) lb
            elim z@(kz , vz) f (k≈kz , vb≤vz) z∈≡lb with LAll.lookup b≤c z∈≡lb
            elim z@(kz , vz) f (k≈kz , vb≤vz) z∈≡la | z≤c = anyEliminate lc elim' z≤c
              where
                elim' : AnyEliminator {ℓQ = l0} |E| (kv ∈' (a ∨' c)) (z ≤e_) lc
                elim' w@(kw , vw) f (kz≈kw , vz≤vw) w∈≡lc = 
                  from ⟨$⟩ (va , vw , kva∈a , (inj₁ $ LAny.map aux w∈≡lc) , v≤va∨vw)
                  where
                    open Equivalence (e∈a∨b⇔P∨ a c kv)
                    open BoundedJoinSemilattice V 
                    open import Relation.Binary.Properties.JoinSemilattice
                   
                    k≈kw : k ≈k kw
                    k≈kw = ≈k-trans k≈kz kz≈kw
                    
                    vb≤vw : vb ≤v vw
                    vb≤vw = ≤v-trans vb≤vz vz≤vw

                    v≤va∨vw : v ≤v (va ∨v vw)
                    v≤va∨vw = ≤v-trans v≤va∨vb (∨-monotonic joinSemiLattice ≤v-refl vb≤vw)
                  
                    aux : {x : |E|} → (kw , vw) ≡ x → (k , vw) ≤e x
                    aux {x} PE.refl = k≈kw , ≤v-refl
        tab {kv@(k , v)} kv∈a∨b | va , vb , kva∈a , inj₂ vb≈⊥ , v≤va∨vc = 
          from ⟨$⟩ (va , ⊥v , kva∈a , inj₂ ≈v-refl , ≤-respʳ-≈ (∨-cong joinSemiLattice ≈v-refl vb≈⊥) v≤va∨vc ) 
          where
            open Equivalence (e∈a∨b⇔P∨ a c kv)          
            open BoundedJoinSemilattice V 
            open import Relation.Binary.Properties.JoinSemilattice
        --]]]

        p : All (λ z → z ∈' (a ∨' c)) (proj₁ $ (a ∨' b))
        p = LAll.tabulate tab

        tab' : {kv : |E|} → kv ∈ (proj₁ $ (a ∨' b)) → Any (kv ≤e_) (proj₁ $ a ∨' c)
        --[[[
        tab' {k , v} kv∈a∨b with LAll.lookup p kv∈a∨b
        tab' {k , v} kv∈a∨b | inj₁ kv≤a∨b = kv≤a∨b
        tab' {k , v} kv∈a∨b | inj₂ v≈⊥ = ⊥-elim $ ¬v≈⊥ v≈⊥ 
          where
            ¬v≈⊥ : ¬ (v ≈v ⊥v) 
            ¬v≈⊥ = dict-no⊥ (proj₁ $ a ∨' b) (∨-Dict da db) (k , v) kv∈a∨b
        --]]]
      --]]]
    --]]]

    

    reflexive' : _≈'_ Implies _≤'_
    reflexive' (x , _) = x

    refl' : Reflexive _≤'_
    refl' {l , _} = LAll.tabulate f 
      where
        f : ∀ {x} → x ∈ l → Any (x ≤e_) l
        f {x} x∈l = mapAny p x∈l
          where
            p : ∀ {y} → x ≡ y → x ≤e y
            p {l , d} PE.refl = StrictTotalOrder.Eq.refl K , BoundedJoinSemilattice.refl V

    trans-≤' : Transitive _≤'_
    trans-≤' {l1 , _} {l2 , _} {l3 , _} d1≤d2 d2≤d3 =
      LAll.tabulate tab
      where
        open import Data.List.Membership.Propositional
        open import Data.List.All as LAll
        open import Data.List.Any as LAny

        tab : {x : |E|} → x ∈ l1 → Any (x ≤e_) l3
        tab {x} x∈l1 = anyEliminate l2 elim (LAll.lookup d1≤d2 x∈l1)
          where
            elim : AnyEliminator {ℓQ = l0} |E| (Any (x ≤e_) l3) (x ≤e_) l2
            elim a f x≤a a∈l2 = LAny.map (λ a≤· → trans-≤e x≤a a≤·) (LAll.lookup d2≤d3 a∈l2)

    trans-≈' : Transitive _≈'_
    trans-≈' {d1} {d2} {d3} (l1∼l2 , l2∼l1) (l2∼l3 , l3∼l2) = 
      trans-≤' {d1} {d2} {d3} l1∼l2 l2∼l3 , trans-≤' {d3} {d2} {d1} l3∼l2 l2∼l1 

    sym-≈' : Symmetric _≈'_
    sym-≈' (d1∼d2 , d2∼d1) = (d2∼d1 , d1∼d2)

    antisym-≤' : Antisymmetric _≈'_ _≤'_
    antisym-≤' a≤b b≤a = a≤b , b≤a

{-
▹-poset : Poset l0 l0 l0
▹-poset = 
  record
  { Carrier = Carrier'
  ; _≤_ = _≤'_ 
  ; _≈_ = _≈'_
  ; isPartialOrder = record
    { isPreorder = record
      { reflexive = λ {x} {y} → reflexive' {x} {y}
      ; trans = λ {x} {y} {z} → trans-≤' {x} {y} {z}
      ; isEquivalence = record
        { trans = λ {x} {y} {z} → trans-≈' {x} {y} {z}
        ; refl = λ {x} → refl' {x} , refl' {x}
        ; sym = λ {x} {y} → sym-≈' {x} {y}
        }
      }
      ; antisym = λ {x} {y} → antisym-≤' {x} {y}
    }
  } 
  where
    open import Data.List.Any renaming (map to mapAny)
    open import Data.List.All renaming (map to mapAll ; tabulate to tabulateAll)
    open import Data.List.Membership.Propositional
    open import Relation.Binary renaming (_⇒_ to _Implies_)

    Carrier' : Set
    Carrier' = ▹-Ty


    trans-≤e : Transitive _≤e_
    trans-≤e (k1≈k2 , v1≤v2) (k2≈k3 , v2≤v3) = 
      StrictTotalOrder.Eq.trans K k1≈k2 k2≈k3 , BoundedJoinSemilattice.trans V v1≤v2 v2≤v3

    _≤'_ : Carrier' → Carrier' → Set
    (l₁ , _) ≤' (l₂ , _) = All (λ e₁ → Any (λ e₂ → e₁ ≤e e₂) l₂) l₁

    _≈'_ : Carrier' → Carrier' → Set
    i ≈' j = (i ≤' j) × (j ≤' i)

    reflexive' : _≈'_ Implies _≤'_
    reflexive' (x , _) = x

    refl' : Reflexive _≤'_
    refl' {l , _} = tabulateAll f 
      where
        f : ∀ {x} → x ∈ l → Any (x ≤e_) l
        f {x} x∈l = mapAny p x∈l
          where
            p : ∀ {y} → x ≡ y → x ≤e y
            p {l , d} PE.refl = StrictTotalOrder.Eq.refl K , BoundedJoinSemilattice.refl V

    trans-≤' : Transitive _≤'_
    trans-≤' {l1 , _} {l2 , _} {l3 , _} d1≤d2 d2≤d3 =
      LAll.tabulate tab
      where
        open import Data.List.Membership.Propositional
        open import Data.List.All as LAll
        open import Data.List.Any as LAny

        tab : {x : |E|} → x ∈ l1 → Any (x ≤e_) l3
        tab {x} x∈l1 = anyEliminate l2 elim (LAll.lookup d1≤d2 x∈l1)
          where
            elim : AnyEliminator {ℓQ = l0} |E| (Any (x ≤e_) l3) (x ≤e_) l2
            elim a f x≤a a∈l2 = LAny.map (λ a≤· → trans-≤e x≤a a≤·) (LAll.lookup d2≤d3 a∈l2)

    trans-≈' : Transitive _≈'_
    trans-≈' {d1} {d2} {d3} (l1∼l2 , l2∼l1) (l2∼l3 , l3∼l2) = 
      trans-≤' {d1} {d2} {d3} l1∼l2 l2∼l3 , trans-≤' {d3} {d2} {d1} l3∼l2 l2∼l1 

    sym-≈' : Symmetric _≈'_
    sym-≈' (d1∼d2 , d2∼d1) = (d2∼d1 , d1∼d2)

    antisym-≤' : Antisymmetric _≈'_ _≤'_
    antisym-≤' a≤b b≤a = a≤b , b≤a
-}
▹-poset : Poset l0 l0 l0
▹-poset = BoundedJoinSemilattice.poset ▹-semilat
