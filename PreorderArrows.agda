module PreorderArrows where

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.Lattice
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum
open import Data.Sum.Relation.Pointwise hiding (₁∼₁ ; ₂∼₂)
open import Data.Product
open import Data.List
open import Data.List.All
open import Function using (_$_)

open import Util
open import Deltas
open import FreeForgetfulAdjunction
open import FreeSemilattice hiding (∷-Free ; []-Free ; FP-BJS ; ⊥ ; _∨_)
open import SemScalars
open import Scalars
open import Preorders

----- products
--[[[

_⟨×⟩_ : {P Q R S : Preorder l0 l0 l0} → P ⇒ Q → R ⇒ S → (×-preorder P R) ⇒ (×-preorder Q S)
--[[[
_⟨×⟩_ {P} {Q} {R} {S} f g = record 
  { fun = fun
  ; monotone = monotone
  }  
  where
    open Preorder

    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q
    |R| = Preorder.Carrier R
    |S| = Preorder.Carrier S

    |f| : |P| → |Q|
    |f| = _⇒_.fun f

    |g| : |R| → |S|
    |g| = _⇒_.fun g

    fun : |P| × |R| → |Q| × |S|
    fun (p , r) = |f| p , |g| r

    monotone : _∼_ (×-preorder P R) =[ fun ]⇒ _∼_ (×-preorder Q S)
    monotone {p₁ , r₁} {p₂ , r₂} (p₁≤p₂ , r₁≤r₂) = (_⇒_.monotone f p₁≤p₂ , _⇒_.monotone g r₁≤r₂)
--]]]

⟨_,_⟩ : {P Q R : Preorder l0 l0 l0} → P ⇒ Q → P ⇒ R → P ⇒ (×-preorder Q R)
--[[[
⟨_,_⟩ {P} {Q} {R} f g = record
  { fun = λ p → ( |f| p , |g| p )
  ; monotone = λ {p₁} {p₂} p₁≤p₂ → _⇒_.monotone f p₁≤p₂ , _⇒_.monotone g p₁≤p₂
  }
  where
    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q
    |R| = Preorder.Carrier R

    |f| : |P| → |Q|
    |f| = _⇒_.fun f

    |g| : |P| → |R|
    |g| = _⇒_.fun g
--]]]

π₁ : {P Q : Preorder l0 l0 l0} → (×-preorder P Q) ⇒ P
--[[[
π₁ {P} {Q} = record
  { fun = fun
  ; monotone = monotone
  }
  where
    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q

    fun : |P| × |Q| → |P|
    fun = proj₁

    monotone : (Preorder._∼_ (×-preorder P Q)) =[ fun ]⇒ (Preorder._∼_ P)
    monotone {p₁ , q₁} {p₂ , q₂} (p₁≤p₂ , q₁≤q₂) = p₁≤p₂ 
--]]]

π₂ : {P Q : Preorder l0 l0 l0} → (×-preorder P Q) ⇒ Q
--[[[
π₂ {P} {Q} = record
  { fun = fun
  ; monotone = monotone
  }
  where
    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q

    fun : |P| × |Q| → |Q|
    fun = proj₂

    monotone : (Preorder._∼_ (×-preorder P Q)) =[ fun ]⇒ (Preorder._∼_ Q)
    monotone {p₁ , q₁} {p₂ , q₂} (p₁≤p₂ , q₁≤q₂) = q₁≤q₂ 
--]]]

assoc : (P Q R : Preorder l0 l0 l0) → (×-preorder (×-preorder P Q) R) ⇒ (×-preorder P (×-preorder Q R)) 
assoc P Q R = record
  { fun = fun
  ; monotone = monotone
  }
  where
    open Preorder
    |P| = Carrier P
    |Q| = Carrier Q
    |R| = Carrier R

    fun : ((|P| × |Q|) × |R|) → (|P| × (|Q| × |R|))
    fun ((P , Q) , R) = (P , (Q , R))

    monotone : (_∼_ (×-preorder (×-preorder P Q) R)) =[ fun ]⇒ (_∼_ (×-preorder P (×-preorder Q R)))
    monotone ((p₁∼p₂ , q₁∼q₂) , r₁∼r₂) = (p₁∼p₂ , (q₁∼q₂ , r₁∼r₂))
--]]]


----- sums
--[[[
-- sum (coproduct) property
[[+]] : {A B C : Preorder l0 l0 l0} → (×-preorder (⇒-preorder A C) (⇒-preorder B C)) ⇒ (⇒-preorder (⊎-preorder0 A B) C)
[[+]] {A} {B} {C} =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    preorder-A⊎B = ⊎-preorder0 A B

    fun : (Preorder.Carrier (×-preorder (⇒-preorder A C) (⇒-preorder B C))) → (Preorder.Carrier (⇒-preorder preorder-A⊎B C))
    fun (a⇒c , b⇒c) = record
      { fun = fun'
      ; monotone = monotone'
      }
      where
        fun' : (Preorder.Carrier preorder-A⊎B) → (Preorder.Carrier C)
        fun' (inj₁ a) = _⇒_.fun a⇒c a
        fun' (inj₂ b) = _⇒_.fun b⇒c b
 
        monotone' : (Preorder._∼_ preorder-A⊎B) =[ fun'  ]⇒ (Preorder._∼_ C)
        monotone' {inj₁ a₁} {inj₁ a₂} (inj₁ a₁≤a₂) = _⇒_.monotone a⇒c a₁≤a₂
        monotone' {inj₂ b₁} {inj₂ b₂} (inj₂ b₁≤b₂) = _⇒_.monotone b⇒c b₁≤b₂

    monotone : (Preorder._∼_ (×-preorder (⇒-preorder A C) (⇒-preorder B C))) =[ fun ]⇒ (Preorder._∼_ (⇒-preorder preorder-A⊎B C))
    monotone {a⇒c₁ , b⇒c₁} {a⇒c₂ , b⇒c₂} (a⇒c₁≤a⇒c₂ , b⇒c₁≤b⇒c₂) {inj₁ a} = a⇒c₁≤a⇒c₂ {a}
    monotone {a⇒c₁ , b⇒c₁} {a⇒c₂ , b⇒c₂} (a⇒c₁≤a⇒c₂ , b⇒c₁≤b⇒c₂) {inj₂ b} = b⇒c₁≤b⇒c₂ {b}

κ₁ : {P Q : Preorder l0 l0 l0} → P ⇒ (⊎-preorder P Q)
κ₁ {P} {Q} =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    open Preorder
    fun : (Carrier P) → (Carrier (⊎-preorder P Q))
    fun p = inj₁ p

    monotone : (_∼_ P) =[ fun ]⇒ (_∼_ (⊎-preorder P Q))
    monotone {p₁} {p₂} p₁∼p₂ = inj₁ p₁∼p₂

κ₂ : {P Q : Preorder l0 l0 l0} → Q ⇒ (⊎-preorder P Q)
κ₂ {P} {Q} =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    open Preorder
    fun : (Carrier Q) → (Carrier (⊎-preorder P Q))
    fun q = inj₂ q

    monotone : (_∼_ Q) =[ fun ]⇒ (_∼_ (⊎-preorder P Q))
    monotone {p₁} {p₂} p₁∼p₂ = inj₂ p₁∼p₂

_⟨+⟩_ : {P Q R S : Preorder l0 l0 l0} → P ⇒ R → Q ⇒ S → (⊎-preorder P Q) ⇒ (⊎-preorder R S)
_⟨+⟩_ {P} {Q} {R} {S} f g = record
  { fun = fun
  ; monotone = monotone
  }
  where
    open Preorder
    |P| = Carrier P
    |Q| = Carrier Q
    |R| = Carrier R
    |S| = Carrier S

    fun : (|P| ⊎ |Q|) → (|R| ⊎ |S|)
    fun (inj₁ p) = inj₁ ((_⇒_.fun f) p)
    fun (inj₂ q) = inj₂ ((_⇒_.fun g) q)

    monotone : (_∼_ (⊎-preorder P Q)) =[ fun ]⇒ (_∼_ (⊎-preorder R S))
    monotone {inj₁ p₁} {inj₁ p₂} (inj₁ p₁∼p₂) = inj₁ (_⇒_.monotone f p₁∼p₂)  
    monotone {inj₂ q₁} {inj₂ q₂} (inj₂ q₁∼q₂) = inj₂ (_⇒_.monotone g q₁∼q₂)

--]]]

----- exponentials
--[[[

Λ : {P Q R : Preorder l0 l0 l0} → ((×-preorder P Q) ⇒ R) → Q ⇒ (⇒-preorder P R)
--[[[
Λ {P} {Q} {R} P×Q⇒R = record
  { fun = fun
  ; monotone = monotone
  }
  where
    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q
    |R| = Preorder.Carrier R

    fun : (Preorder.Carrier Q) → (P ⇒ R)
    fun q = record
      { fun = funRes
      ; monotone = monoRes
      }
      where
        funRes : |P| → |R|
        funRes p = (_⇒_.fun P×Q⇒R) (p , q)

        monoRes : (Preorder._∼_ P) =[ funRes ]⇒ (Preorder._∼_ R)
        monoRes {p₁} {p₂} p₁≤p₂ = _⇒_.monotone P×Q⇒R (p₁≤p₂ , Preorder.refl Q)

    monotone : (Preorder._∼_ Q) =[ fun ]⇒ (Preorder._∼_ (⇒-preorder P R))
    monotone {q₁} {q₂} q₁≤q₂ {p} = _⇒_.monotone P×Q⇒R (Preorder.refl P , q₁≤q₂)

precomp : {P Q R : Preorder l0 l0 l0} → (P ⇒ Q) → (⇒-preorder Q R) ⇒ (⇒-preorder P R)
precomp {P} {Q} {R} (record {fun = p→q ; monotone = p→q-monotone}) =
  record
  { fun = fun
  ; monotone = λ {f₁} {f₂} → monotone {f₁} {f₂}
  }
  where
    open Preorder
    |P| = Carrier P
    |Q| = Carrier Q
    |R| = Carrier R
    
    fun : (Q ⇒ R) → (P ⇒ R)
    fun (record {fun = q→r ; monotone = q→r-monotone}) =
      record
      { fun = p→r
      ; monotone = p→r-monotone
      }
      where
        p→r : |P| → |R|
        p→r p = q→r (p→q p)

        p→r-monotone : (_∼_ P) =[ p→r ]⇒ (_∼_ R)
        p→r-monotone {p₁} {p₂} p₁≤p₂ = q→r-monotone (p→q-monotone p₁≤p₂) 

    monotone : (_∼_ $ ⇒-preorder Q R) =[ fun ]⇒ (_∼_ $ ⇒-preorder P R)
    monotone {f₁} {f₂} f₁≤f₂ {p} = f₁≤f₂
--]]]

ev : {A B : Preorder l0 l0 l0} → ((×-preorder A (⇒-preorder A B)) ⇒ B)
--[[[
ev {A} {B} = 
  record
  { fun = fun
  ; monotone = λ {x} {y} → monotone {x} {y}
  }
  where
    |A| = Preorder.Carrier A
    |B| = Preorder.Carrier B

    fun : (|A| × (A ⇒ B)) → |B|
    fun (a , f) = _⇒_.fun f a

    monotone : (Preorder._∼_ (×-preorder A (⇒-preorder A B))) =[ fun ]⇒ (Preorder._∼_ B)
    monotone {a₁ , f₁} {a₂ , f₂} (a₁≤a₂ , f₁≤f₂) = 
      begin
        |f₁| a₁ ∼⟨ _⇒_.monotone f₁ a₁≤a₂ ⟩
        |f₁| a₂ ∼⟨ f₁≤f₂ ⟩
        |f₂| a₂
       ∎ 
      where
        open import Relation.Binary.PreorderReasoning B
        |f₁| = _⇒_.fun f₁
        |f₂| = _⇒_.fun f₂
--]]]

--]]]

----- dictionaries
--[[[

▹-sng : (P : Poset l0 l0 l0) → (T : StrictTotalOrder l0 l0 l0) → 
          (eq : (poset→setoid P) ≡ StrictTotalOrder.Eq.setoid T) →
          (S : BoundedJoinSemilattice l0 l0 l0) → 
          (D : DeltaPoset {l0} {l0} {l0} {l0}) → (f : S ⇉ FreeSemilattice.FP-BJS D) → 
          (×-preorder (⟦ qAny q⟧ (Poset.preorder P)) (BoundedJoinSemilattice.preorder S)) ⇒ (▹-preorder T S)
--[[[
▹-sng P T PE.refl S D f =
  record
  { fun = fun 
  ; monotone = monotone
  }
  where
    open import Data.List.All
    open import SemilatIso
    open import Dictionary T S hiding (<-respʳ-≈)
    open import Relation.Binary.Lattice
    open import Data.List
    open import FreeSemilattice D 
      renaming (⊥ to ⊥ₛ' ; _≈_ to _≈ₛ'_ ; ≈-trans to ≈ₛ'-trans ; ≈-sym to ≈ₛ'-sym ;
                ≈-reflexive to ≈ₛ'-reflexive ; _≤_ to _≤ₛ'_)
    open Preorder
    open Poset P renaming (_≈_ to _≈ₚ_ ; _≤_ to _≤ₚ_ ; antisym to ≤ₚ-antisym)

    open BoundedJoinSemilattice S renaming (_≈_ to _≈ₛ_ ; ⊥ to ⊥ₛ )

    |P| = Poset.Carrier P
    |S| = BoundedJoinSemilattice.Carrier S
    |T| = StrictTotalOrder.Carrier T
    |f| = proj₁ f
    |f|-≈ = proj₁ $ proj₂ f

    fun : |P| × |S| → Σ[ l ∈ (List $ |T| × |S|) ] (IsDict l)
    --[[[
    fun (p , s) with keep (|f| s) 
    fun (p , s) | ([] , []-Free) , _ = [] , []-Dict
    fun (p , s) | (h ∷ l' , ∷-Free .h .l' min incomp f') , fs≡h∷l' = 
      ((p , s) ∷ []) , (∷-Dict (p , s) [] [] ¬s≈⊥ []-Dict)  
      where
        open import Relation.Nullary

        ¬s≈⊥ : ¬ (s ≈ₛ ⊥ₛ)  
        ¬s≈⊥ s≈⊥ with ⊥≈h∷l'
          where
            f⊥≈⊥ : (|f| ⊥ₛ) ≈ₛ' ⊥ₛ'
            f⊥≈⊥ = proj₁ $ proj₂ $ proj₂ f

            fs≈⊥ : (|f| s) ≈ₛ' ⊥ₛ'
            fs≈⊥ = ≈ₛ'-trans {|f| s} {|f| ⊥ₛ} {⊥ₛ'}  (|f|-≈ s ⊥ₛ s≈⊥) f⊥≈⊥ 

            ⊥≈h∷l' : ⊥ₛ' ≈ₛ' (h ∷ l' , ∷-Free h l' min incomp f')
            ⊥≈h∷l' = 
              ≈ₛ'-trans {⊥ₛ'} {|f| s} {h ∷ l' , ∷-Free h l' min incomp f'} 
                (≈ₛ'-sym {|f| s} {⊥ₛ'} fs≈⊥) 
                (≈ₛ'-reflexive fs≡h∷l')

        ¬s≈⊥ s≈⊥ | ()
    --]]]

    monotone : (_∼_ $ ×-preorder (⟦ qAny q⟧ (Poset.preorder P))  (BoundedJoinSemilattice.preorder S))
               =[ fun ]⇒ 
               (_∼_ $ ▹-preorder T S)
    --[[[
    monotone {p₁ , s₁} {p₂ , s₂} ((p₁≤p₂ , p₂≤p₁) , s₁≤s₂) with keep (|f| s₁) | keep (|f| s₂)
    monotone {p₁ , s₁} {p₂ , s₂} ((p₁≤p₂ , p₂≤p₁) , s₁≤s₂) | ([] , []-Free) , _ | _ , _ = []
    monotone {p₁ , s₁} {p₂ , s₂} ((p₁≤p₂ , p₂≤p₁) , s₁≤s₂) | 
             (h1 ∷ t1 , ∷-Free h1 t1 min1 incomp1 f1) , q1 | 
             ([] , []-Free) , q2 = 
      ⊥-elim $ ¬Any[] (LAll.lookup p (here PE.refl))
      where
        open import Data.List.Any using (here)
        open import Data.List.All as LAll
        open import Data.List.Any.Properties
        open import Data.Empty
        fs1≤fs2 = ⇉-mono {S = S} {T = FP-BJS} f s₁≤s₂
        p : (h1 ∷ t1 , ∷-Free h1 t1 min1 incomp1 f1) ≤ₛ' ([] , []-Free)
        p = 
          begin 
            (h1 ∷ t1 , ∷-Free h1 t1 min1 incomp1 f1) ≡⟨ PE.sym q1 ⟩ 
            (|f| s₁) ≤⟨ fs1≤fs2 ⟩ 
            (|f| s₂) ≡⟨ q2 ⟩
            ([] , []-Free)
           ∎ 
          where
            open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset FP-BJS)
    monotone {p₁ , s₁} {p₂ , s₂} ((p₁≤p₂ , p₂≤p₁) , s₁≤s₂) | 
             (h1 ∷ t1 , ∷-Free h1 t1 min1 incomp1 f1) , _ | 
             (h2 ∷ t2 , ∷-Free h2 t2 min2 incomp2 f2) , _ = 
      here (p₁≈p₂ , s₁≤s₂) ∷ [] 
      where
        open import Data.List.Any using (here)
        p₁≈p₂ : p₁ ≈ₚ p₂
        p₁≈p₂ = ≤ₚ-antisym p₁≤p₂ p₂≤p₁ 
    --]]]
--]]]


▹-elim : (P : Poset l0 l0 l0) → (T : StrictTotalOrder l0 l0 l0) → 
         (eq : (poset→setoid P) ≡ StrictTotalOrder.Eq.setoid T) →
         (valS : BoundedJoinSemilattice l0 l0 l0) → (targetS : BoundedJoinSemilattice l0 l0 l0) →  
         (×-preorder (▹-preorder T valS) 
                     (⇒-preorder (×-preorder (×-preorder (⟦ qAny q⟧ (Poset.preorder P)) (BoundedJoinSemilattice.preorder valS))
                                              (BoundedJoinSemilattice.preorder targetS))
                                 (BoundedJoinSemilattice.preorder targetS))) 
         ⇒
         (BoundedJoinSemilattice.preorder targetS)
▹-elim P T PE.refl valS targetS = 
  record
  { fun = fun 
  ; monotone = monotone
  }
  where
    open import Relation.Binary.Lattice
    open import Data.List
    open import Dictionary T valS hiding (<-respʳ-≈)
    _<k_ = StrictTotalOrder._<_ T

    P' = Poset.preorder P
    valS' = BoundedJoinSemilattice.preorder valS
    targetS' = BoundedJoinSemilattice.preorder targetS

    |P| = Preorder.Carrier P'
    |valS| = BoundedJoinSemilattice.Carrier valS
    |targetS| = BoundedJoinSemilattice.Carrier targetS
    |T▹valS| = Preorder.Carrier (▹-preorder T valS)


    fun : |T▹valS| × ((×-preorder (×-preorder (⟦ qAny q⟧ P') valS') targetS') ⇒ targetS') → |targetS|
    fun (([] , []-Dict) , _) = BoundedJoinSemilattice.⊥ targetS
    fun (((k , v) ∷ t , ∷-Dict _ _ _ _ dt) , f@(record {fun = fun' ; monotone = _})) =
      (fun' ((k , v), acc)) ∨ acc 
      where
        acc : |targetS|
        acc = fun ((t , dt), f)

        _∨_ : |targetS| → |targetS| → |targetS|
        _∨_ = BoundedJoinSemilattice._∨_ targetS

    open Preorder using (_∼_)

    monotone : (_∼_ (×-preorder (▹-preorder T valS) 
                                (⇒-preorder (×-preorder (×-preorder (⟦ qAny q⟧ P') valS') targetS') targetS'))) 
               =[ fun ]⇒ (_∼_ targetS')
    monotone {([] , []-Dict) , f1} {a2} (d1≤d1 , b1≤b1) = BoundedJoinSemilattice.minimum targetS (fun a2)
      where
        open import Relation.Binary.Properties.BoundedJoinSemilattice
    monotone {(h1 ∷ t1 , ∷-Dict h1 t1 min1 ¬⊥1 dt1) , record { monotone = mono1 }} {([] , []-Dict) , record { monotone = mono2 }} (h1≤l2 ∷ t2≤l2 , b1≤b2) =
      ⊥-elim $ ¬Any[] h1≤l2
      where
        open import Data.List.Any.Properties using (¬Any[])
        open import Data.Empty using (⊥-elim)
    monotone {((k1 , v1) ∷ t1 , ∷-Dict h1 t1 min1 ¬⊥1 dt1) , record { monotone = mono1 }} {((k2 , v2) ∷ t2 , ∷-Dict h2 t2 min2 ¬⊥2 dt2) , record { monotone = mono2 }} (d1≤d2 , b1≤b2) with cmp k1 k2
      where
        open IsStrictTotalOrder (StrictTotalOrder.isStrictTotalOrder T) renaming (compare to cmp) 
    monotone {((k1 , v1) ∷ t1 , ∷-Dict h1 t1 min1 ¬⊥1 dt1) , record { monotone = mono1 }} {(l2@(h2 ∷ t2)  , ∷-Dict h2 t2 min2 ¬⊥2 dt2) , record { monotone = mono2 }} (h1≤l2 ∷ t1≤l2 , b1≤b2) | tri< k1<k2 _ _ = 
      --[[[
      ⊥-elim $ anyEliminate l2 elim h1≤l2
      where
        open import Data.Empty using (⊥ ; ⊥-elim)
        open import Data.List.Any using (here ; there)
        open StrictTotalOrder.Eq T renaming (reflexive to reflexiveₖ)
        open StrictTotalOrder T renaming (irrefl to irreflₖ ; trans to transₖ)

        elim : AnyEliminator {ℓQ = l0} (|P| × |valS|) ⊥ ((k1 , v1) ≤e_) l2
        elim (kz , vz) f (k1≈kz , v1≤vz) (here PE.refl) = irreflₖ k1≈kz k1<k2
        elim (kz , vz) f (k1≈kz , v1≤vz) (there z∈≡t2) = irreflₖ k1≈kz k1<kz
          where
            open import Data.List.All as LAll
            k1<kz : k1 <k kz
            k1<kz = transₖ k1<k2 (LAll.lookup min2 z∈≡t2)
      --]]]
    monotone {((k1 , v1) ∷ t1 , ∷-Dict h1 t1 min1 ¬⊥1 dt1) , f1@(record { fun = fun1 ; monotone = mono1 })} {(l2@((k2 , v2) ∷ t2) , ∷-Dict h2 t2 min2 ¬⊥2 dt2) , f2@(record { fun = fun2 ; monotone = mono2 })} ((h1≤d2 ∷ t1≤d2) , b1≤b2) | tri≈ _ k1≈k2 _ =
      --[[[
      let
        monotone-rec : fun ((t1 , dt1) , f1) ≤s fun ((t2 , dt2) , f2)
        monotone-rec = monotone {(t1 , dt1) , f1} {(t2 , dt2) , f2} (t1≤t2 , b1≤b2)

        fh1≤fh2 : fun1 ((k1 , v1) , acc1) ≤s fun2 ((k2 , v2) , acc2) 
        fh1≤fh2 = 
          begin
            fun1 ((k1 , v1) , acc1) ≤⟨ mono1 ((((≤k-reflexive k1≈k2 , ≤k-reflexive (≈k-sym k1≈k2)) , v1≤v2) , monotone-rec)) ⟩
            fun1 ((k2 , v2) , acc2) ≤⟨ b1≤b2 ⟩
            fun2 ((k2 , v2) , acc2)
           ∎ 
      in
      ∨-monotonic (BoundedJoinSemilattice.joinSemilattice targetS) fh1≤fh2 monotone-rec
      where
        open import Relation.Binary.Properties.JoinSemilattice using (∨-monotonic)
        _≤s_ = BoundedJoinSemilattice._≤_ targetS

        open Poset P renaming (reflexive to ≤k-reflexive)
        open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset targetS)

        t1≤t2 : Poset._≤_ ▹-poset (t1 , dt1) (t2 , dt2)
        --[[[
        t1≤t2 = LAll.tabulate p 
          where
            open import Data.List.Any as LAny
            open import Data.List.All as LAll
            open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
            open StrictTotalOrder.Eq T renaming (trans to ≈k-trans)
            open StrictTotalOrder T using (<-respʳ-≈ ; irrefl)
            
 
            p : {kv1 : |K| × |V|} → (kv1 ∈≡ t1) → (Any (kv1 ≤e_) t2)
            p {k1' , v1'} kv1∈≡t1 with LAll.lookup t1≤d2 kv1∈≡t1 
            p {k1' , v1'} kv1∈≡t1 | here (k1'≈k2 , v1'≤v2) = 
             ⊥-elim $ irrefl k1≈k2 k1<k2
              where
                open import Data.Empty using (⊥-elim)

                k1<k1' : k1 <k k1'
                k1<k1' = LAll.lookup min1 kv1∈≡t1

                k1<k2 : k1 <k k2
                k1<k2 = <-respʳ-≈ k1'≈k2 k1<k1'
            p {k1' , v1'} kv1∈≡t1 | there kv1≤t2 = kv1≤t2
        --]]]

        acc1 : |targetS|
        acc1 = fun ((t1 , dt1) , f1)

        acc2 : |targetS|
        acc2 = fun ((t2 , dt2) ,  f2)

        h1≤h2 : (k1 , v1) ≤e (k2 , v2)
        h1≤h2 = anyEliminate l2 elim h1≤d2 
          where 
            open import Data.List.Any using (here ; there)
            open import Data.List.All as LAll
            open import Data.Empty using (⊥-elim)
            open StrictTotalOrder T using (<-respʳ-≈ ; irrefl)

            elim : AnyEliminator {ℓQ = l0} (|K| × |V|) ((k1 , v1) ≤e (k2 , v2)) ((k1 , v1) ≤e_) l2
            elim (kz , vz) f k1v1≤kzvz (here PE.refl) = k1v1≤kzvz
            elim (kz , vz) f (k1≈kz , v1≤vz) (there kzvz∈t2) = ⊥-elim $ irrefl (≈k-sym k1≈k2) k2<k1
              where
                k2<kz : k2 <k kz
                k2<kz = LAll.lookup min2 kzvz∈t2
                
                k2<k1 : k2 <k k1
                k2<k1 = <-respʳ-≈ (≈k-sym k1≈kz) k2<kz 

        v1≤v2 : v1 ≤v v2
        v1≤v2 = proj₂ h1≤h2
      --]]]
    monotone {d1@((k1 , v1) ∷ t1 , ∷-Dict h1 t1 min1 ¬⊥1 dt1) , f1@(record { fun = fun1 ; monotone = mono1 })} {d2@((k2 , v2) ∷ t2 , ∷-Dict h2 t2 min2 ¬⊥2 dt2) , f2@(record { fun = fun2 ; monotone = mono2 })} (kv1≤d2 ∷ t1≤d2  , b1≤b2) | tri> _ _ k2<k1 = 
      let
        fd1≤ft2 : (fun (d1 , f1) ≤s acc2)
        fd1≤ft2 = monotone {d1 , f1} {(t2 , dt2) , f2} (d1≤t2 , b1≤b2)
      in
      begin
        fun (d1 , f1) ≤⟨ fd1≤ft2 ⟩
        fun ((t2 , dt2) , f2) ≤⟨ proj₁ $ proj₂ $ supremum (fun2 ((k2 , v2) , acc2)) acc2 ⟩
        fun (d2 , f2)
       ∎
      where
        open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
        open import Data.List.Any as LAny using (Any ; here ; there ; map)
        open import Data.List.All as LAll using (tabulate ; lookup)
        open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset targetS)
        open import Relation.Binary.Lattice
        open BoundedJoinSemilattice (targetS) using (supremum)

        _≤d_ = Poset._≤_ ▹-poset
        ≤d-trans = Poset.trans ▹-poset
        ≤d-refl = Poset.refl ▹-poset
        _≤s_ = BoundedJoinSemilattice._≤_ targetS

        acc2 : |targetS|
        acc2 = fun ((t2 , dt2) , f2) 

        d1≤t2 : (d1 ≤d (t2 , dt2))
        --[[[
        d1≤t2 = LAll.tabulate p
          where
            p : {kv1' : |K| × |V|} → kv1' ∈≡ ((k1 , v1) ∷ t1) →  Any (kv1' ≤e_) t2
            p {k1' , v1'} (here PE.refl) = 
              anyEliminate ((k2 , v2) ∷ t2) elim kv1≤d2 
              where
                elim : AnyEliminator {ℓQ = l0} (|K| × |V|) (Any ((k1 , v1) ≤e_) t2) ((k1 , v1) ≤e_) ((k2 , v2) ∷ t2)
                elim (kz , vz) f (k1≈kz , _) (here PE.refl) = ⊥-elim $ irrefl ≈k-refl (<-respʳ-≈ k1≈kz k2<k1)  
                  where
                    open import Data.Empty using (⊥-elim)
                    open StrictTotalOrder T using (<-respʳ-≈ ; irrefl)
                elim (kz , vz) f k1v1≤kzvz (there kzvz∈t2) = 
                  LAny.map (λ kzvz≡· → ≤e-trans k1v1≤kzvz (≤e-reflexive kzvz≡·)) kzvz∈t2 

            p {k1' , v1'} (there k1'v1'∈t1) with k1'v1≤d2
              where
                k1'v1≤d2 : Any ((k1' , v1') ≤e_) ((k2 , v2) ∷ t2)
                k1'v1≤d2 = LAll.lookup t1≤d2 k1'v1'∈t1
            p {k1' , v1'} (there k1'v1'∈t1) | here (k1'≈k2 , v1'≤v2) = 
              ⊥-elim $ <k-irrefl (≈k-reflexive PE.refl) (<k-trans k1<k1' k1'<k1)
              where
                open import Data.Empty using (⊥-elim)
                open StrictTotalOrder T renaming (trans to <k-trans ; irrefl to <k-irrefl ; <-respˡ-≈ to <k-respˡ-≈k)
                open StrictTotalOrder.Eq T renaming (reflexive to ≈k-reflexive)

                k1'<k1 : k1' <k k1
                k1'<k1 = <k-respˡ-≈k (≈k-sym k1'≈k2) k2<k1

                k1<k1' : k1 <k k1'
                k1<k1' = LAll.lookup min1 k1'v1'∈t1
            p {k1' , v1'} (there k1'v1'∈t1) | there h1≤t2 = h1≤t2
          --]]]
            
--]]]

----- monotone partiality 
--[[[
module _ where
  open import Data.Unit
  open import Data.Unit.Properties
  open import Data.Sum.Relation.LeftOrder
  open Preorder using (_∼_)
  
  -- unit for the monotone partiality monad
  pure : (P : Preorder l0 l0 l0) → P ⇒ (partial-preorder P)
  pure P = 
    record
    { fun = fun
    ; monotone = monotone
    }
    where
      |P| = Preorder.Carrier P
      |Pᵀ| = |P| ⊎ ⊤ 

      fun : |P| → |Pᵀ|
      fun p = inj₁ p

      monotone : (_∼_ P) =[ fun ]⇒ (_∼_ $ ⊎-<-preorder P (Poset.preorder ≤-poset))
      monotone {p₁} {p₂} p₁∼p₂ = ₁∼₁ p₁∼p₂

  -- tensorial strength of the strong monad underlying monotone partiality
  tstr : {P Q : Preorder l0 l0 l0} → (×-preorder P (partial-preorder Q)) ⇒ (partial-preorder (×-preorder P Q))
  tstr {P} {Q} = record
    { fun = fun
    ; monotone = monotone
    }
    where
      |P| = Preorder.Carrier P
      |Q| = Preorder.Carrier Q

      fun : |P| × (|Q| ⊎ ⊤) → (|P| × |Q|) ⊎ ⊤ 
      fun (p , inj₁ q) = inj₁ (p , q)
      fun (p , inj₂ tt) = inj₂ tt
      
      monotone : (_∼_ (×-preorder P (partial-preorder Q))) =[ fun ]⇒ (_∼_ (partial-preorder (×-preorder P Q)))
      monotone {p₁ , inj₁ q₁} {p₂ , inj₁ q₂} (p₁∼p₂ , ₁∼₁ q₁∼q₂) = ₁∼₁ (p₁∼p₂ , q₁∼q₂)
      monotone {p₁ , inj₁ q₁} {p₂ , inj₂ tt} (p₁∼p₂ , ₁∼₂) = ₁∼₂
      monotone {p₁ , inj₂ tt} {p₂ , inj₁ q₂} (p₁∼p₂ , ())
      monotone {p₁ , inj₂ tt} {p₂ , inj₂ tt} (p₁∼p₂ , ₂∼₂ (record {})) = ₂∼₂ (record {})

  ⇒ᵀ : {P Q : Preorder l0 l0 l0} → (P ⇒ Q) → ((partial-preorder P) ⇒ (partial-preorder Q))
  ⇒ᵀ {P} {Q} f = record
    { fun = fun
    ; monotone = monotone
    }
    where
      |P| = Preorder.Carrier P
      |Q| = Preorder.Carrier Q

      |f| = _⇒_.fun f
      |f|-mono = _⇒_.monotone f

      fun : (|P| ⊎ ⊤) → (|Q| ⊎ ⊤)
      fun (inj₁ p) = inj₁ (|f| p)
      fun (inj₂ tt) = inj₂ tt

      monotone : (_∼_ (partial-preorder P)) =[ fun ]⇒ (_∼_ (partial-preorder Q))
      monotone {inj₁ p₁} {inj₁ p₂} (₁∼₁ p₁∼p₂) = ₁∼₁ (|f|-mono p₁∼p₂)
      monotone {inj₁ p₁} {inj₂ tt} ₁∼₂ = ₁∼₂
      monotone {inj₂ tt} {inj₁ p₁} ()
      monotone {inj₂ tt} {inj₂ tt} (₂∼₂ (record {})) = ₂∼₂ (record {}) 

  μ : {P : Preorder l0 l0 l0} → (partial-preorder (partial-preorder P)) ⇒ (partial-preorder P)
  μ {P} = record
    { fun = fun
    ; monotone = monotone
    }
    where
      |P| = Preorder.Carrier P

      fun : ((|P| ⊎ ⊤) ⊎ ⊤) → (|P| ⊎ ⊤)
      fun (inj₁ p) = p
      fun (inj₂ tt) = inj₂ tt
      
      monotone : (_∼_ (partial-preorder (partial-preorder P))) =[ fun ]⇒ (_∼_ (partial-preorder P))
      monotone {inj₁ p₁} {inj₁ p₂} (₁∼₁ p₁∼p₂)  = p₁∼p₂
      monotone {inj₁ (inj₁ p₁)} {inj₂ tt} ₁∼₂ = ₁∼₂
      monotone {inj₁ (inj₂ tt)} {inj₂ tt} ₁∼₂ = ₂∼₂ (record {})
      monotone {inj₂ tt} {inj₁ p} ()
      monotone {inj₂ tt} {inj₂ tt} (₂∼₂ (record {})) = ₂∼₂ (record {})

--]]]

----- ivars
--[[[
module _ where
  -- ivar introduction
  ξ : {T : StrictTotalOrder l0 l0 l0} → {P : Poset l0 l0 l0} → 
      {eq : StrictTotalOrder.Eq.setoid T ≡ poset→setoid P} →
      (⟦ qAny q⟧ $ Poset.preorder P) ⇒ (⌈⌉-preorder T)
  --[[[
  ξ {T} {P} {PE.refl} = record
    { fun = fun
    ; monotone = monotone
    }
    where
      open import IVar T as I
      open Preorder
      P' = Poset.preorder P
      fun : (Preorder.Carrier P') → (Preorder.Carrier $ ⌈⌉-preorder T)
      fun p = (p ∷ [] , ∷-Free p [] [] (λ ()) []-Free)

      monotone : (_∼_ $ ⟦ qAny q⟧ $ P') =[ fun ]⇒ (_∼_ $ ⌈⌉-preorder T)
      monotone {p₁} {p₂} (p₁≤p₂ , p₂≤p₁) = (here (I.⊑-reflexive p₁≈p₂)) ∷ [] 
        where
          open import Data.List.Any using (here)
          p₁≈p₂ : p₁ ≈E p₂ 
          p₁≈p₂ = Poset.antisym P p₁≤p₂ p₂≤p₁ 
  --]]]

  -- ivar eliminatio
  ζ : {T : StrictTotalOrder l0 l0 l0} → {P : Poset l0 l0 l0} → {S : BoundedJoinSemilattice l0 l0 l0} →
      {eq : StrictTotalOrder.Eq.setoid T ≡ poset→setoid P} →
      (×-preorder (⌈⌉-preorder T) (⇒-preorder (⟦ qAny q⟧ $ Poset.preorder P) (BoundedJoinSemilattice.preorder S)))
      ⇒
      (partial-preorder $ BoundedJoinSemilattice.preorder S)
  --[[[
  ζ {T} {P} {S} {PE.refl} = record
    { fun = fun
    ; monotone = monotone 
    } 
    where
      open Preorder
      open import Data.Unit using (⊤ ; tt)
      open import IVar T as I
      -- open import Data.Sum.Relation.Pointwise using (₁∼₁ ; )
      open import Data.Sum.Relation.LeftOrder using (₁∼₁ ; ₁∼₂ ; ₂∼₂)
      open import Data.List.Any.Properties using (¬Any[])
      open import Data.List.Any using (here ; there)
      open import Data.List.All as LAll
      open import Data.Empty using (⊥-elim)
      open import DiscreteDelta T

      |P| = Poset.Carrier P
      |S| = BoundedJoinSemilattice.Carrier S
      |T| = StrictTotalOrder.Carrier T
      <ₜ-irrefl = StrictTotalOrder.irrefl T 
      S' = BoundedJoinSemilattice.preorder S
      P' = Poset.preorder P
      ⊥ₛ = BoundedJoinSemilattice.⊥ S
      _≤ₛ_ = BoundedJoinSemilattice._≤_ S
      _≈ₚ_ = Poset._≈_ P
      ≤ₚ-reflexive = Poset.reflexive P
      ≈ₚ-sym = Poset.Eq.sym P
      ≈ₚ-trans = Poset.Eq.trans P

      fun : ((Preorder.Carrier $ ⌈⌉-preorder T) × ((⟦ qAny q⟧ P') ⇒ S')) → (|S| ⊎ ⊤)
      --[[[
      fun (([] , []-IVar) , _) = inj₁ ⊥ₛ
      fun ((p ∷ [] , ∷-Free p [] [] incomp []-Free) , (record { fun = f })) = 
        inj₁ $ f p
      fun ((p ∷ q ∷ _ , _) , _) = inj₂ tt
      --]]]

      monotone : (_∼_ $ ×-preorder (⌈⌉-preorder T) (⇒-preorder (⟦ qAny q⟧ P') S')) =[ fun ]⇒ (_∼_ $ partial-preorder S')
      --[[[
      monotone {([] , []-Free) , record { fun = f₁ ; monotone = m₁ }} {([] , []-Free) , record { fun = f₂ ; monotone = m₂ }} (p₁≈p₂ , f₁≤f₂) = 
        ₁∼₁ $ BoundedJoinSemilattice.minimum S ⊥ₛ 
      monotone {([] , []-Free) , record { fun = f₁ ; monotone = m₁ }} {(p ∷ [] , ∷-Free p [] [] incomp []-Free) , record { fun = f₂ ; monotone = m₂ }} (p₁≈p₂  , f₁≤f₂) =
        ₁∼₁ $ BoundedJoinSemilattice.minimum S (f₂ p)
      monotone {([] , []-IVar) , record { fun = f₁ ; monotone = m₁ }} {(p ∷ q ∷ _ , _) , record { fun = f₂ ; monotone = m₂ }} (p₁≈p₂  , f₁≤f₂) =
        ₁∼₂
      monotone {(p ∷ _ , _) , record { fun = f₁ ; monotone = m₁ }} {([] , _) , record { fun = f₂ ; monotone = m₂ }} (p₁≈p₂  , f₁≤f₂) = 
        ⊥-elim $ ¬Any[] (LAll.lookup p₁≈p₂ (here PE.refl))
      monotone {(p₁ ∷ [] , ∷-Free p₁ [] [] _ []-Free) , record { fun = f₁ ; monotone = m₁ }} {(p₂ ∷ [] , ∷-Free p₂ [] [] _ []-Free) , record { fun = f₂ ; monotone = m₂ }} ((here (⊑-refl p₁≈p₂)) ∷ _  , f₁≤f₂) = 
        ₁∼₁ f₁p₁≤f₂p₂
        where
          open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset S)

          f₁p₁≤f₂p₂ : f₁ p₁ ≤ₛ f₂ p₂
          f₁p₁≤f₂p₂ = 
            begin
              f₁ p₁ ≤⟨ f₁≤f₂ ⟩
              f₂ p₁ ≤⟨ m₂ ((≤ₚ-reflexive p₁≈p₂ , ≤ₚ-reflexive (≈ₚ-sym p₁≈p₂)) ) ⟩ 
              f₂ p₂
             ∎ 
      monotone {(p₁ ∷ [] , ∷-Free p₁ [] [] _ []-Free) , record { fun = f₁ ; monotone = m₁ }} {(p₂ ∷ [] , ∷-Free p₂ [] [] _ []-Free) , record { fun = f₂ ; monotone = m₂ }} ((there p₁≈[]) ∷ _  , f₁≤f₂) =
        ⊥-elim $ ¬Any[] p₁≈[]
      monotone {(p₁ ∷ [] , ∷-Free p₁ [] [] _ []-Free) , record { fun = f₁ ; monotone = m₁ }} {(p₂ ∷ q₂ ∷ _ , _) , record { fun = f₂ ; monotone = m₂ }} (p₁≈p₂  , f₁≤f₂) = 
        ₁∼₂
      monotone {(p₁ ∷ q₁ ∷ _ , ∷-Free _ _ min1 _ _) , record { fun = f₁ ; monotone = m₁ }} {(p₂ ∷ [] , _) , record { fun = f₂ ; monotone = m₂ }} ((here (⊑-refl p₁≈p₂)) ∷ (here (⊑-refl q₁≈p₂)) ∷ _  , f₁≤f₂) =
        ⊥-elim $ <ₜ-irrefl p₁≈q₁ (LAll.lookup min1 (here PE.refl))
        where
          p₁≈q₁ : p₁ ≈ₚ q₁
          p₁≈q₁ = ≈ₚ-trans p₁≈p₂ (≈ₚ-sym q₁≈p₂) 
      monotone {(p₁ ∷ q₁ ∷ _ , ∷-Free _ _ min1 _ _) , record { fun = f₁ ; monotone = m₁ }} {(p₂ ∷ [] , _) , record { fun = f₂ ; monotone = m₂ }} ((there p₁≈[]) ∷ _ ∷ _  , f₁≤f₂) =
        ⊥-elim $ ¬Any[] p₁≈[]
      monotone {(p₁ ∷ q₁ ∷ _ , ∷-Free _ _ min1 _ _) , record { fun = f₁ ; monotone = m₁ }} {(p₂ ∷ [] , _) , record { fun = f₂ ; monotone = m₂ }} (here _ ∷ (there q₁≈[]) ∷ _  , f₁≤f₂) =
        ⊥-elim $ ¬Any[] q₁≈[]
      monotone {(p₁ ∷ q₁ ∷ _ , ∷-Free _ _ min1 _ _) , record { fun = f₁ ; monotone = m₁ }} {(p₂ ∷ q₂ ∷ _ , _) , record { fun = f₂ ; monotone = m₂ }} (p₁≈p₂  , f₁≤f₂) = 
        ₂∼₂ (record {})
      --]]]
    --]]]
--]]]
