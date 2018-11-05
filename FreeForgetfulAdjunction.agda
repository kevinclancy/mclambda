open import Function using (_$_)
open import Function.Equivalence as FE
open import Function.Equality using (_⟨$⟩_)
open import Data.Empty
open import Data.List
open import Data.List.Properties as LP
open import Data.List.All as LA
open import Data.List.Any as LAny
open import Data.List.Any.Properties as LAP
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE
open import Level

open import Deltas
open import Util
open import Preorders

module FreeForgetfulAdjunction where

BoundedJoinSemilattice0 : Set₁
BoundedJoinSemilattice0 = BoundedJoinSemilattice l0 l0 l0

module _ where
 --anonymous module allows local import of FreeSemilattice.Semilattice
 open import FreeSemilattice.Semilattice

 -- unit of the free/forgetful adjunction
 η : {c ℓ⊑ ℓ< ℓ~ : Level} → (P : DeltaPoset {c} {ℓ⊑} {ℓ<} {ℓ~}) → (p : DeltaPoset.Carrier P) → (BoundedJoinSemilattice.Carrier (FP-BJS P))
 η P p = (p ∷ [] , ∷-Free p [] [] (λ ()) []-Free)
   where
     open import FreeSemilattice.Core P

Monotone : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} → (P : Preorder ℓ₀ ℓ₁ ℓ₂) → (R : Preorder ℓ₃ ℓ₄ ℓ₅) → 
           (Preorder.Carrier P → Preorder.Carrier R) → Set _
Monotone P R f = ∀ {p p' : |P|} → p ∼ₚ p' → (f p) ∼ᵣ (f p')    
  where
    open Preorder P renaming (_∼_ to _∼ₚ_ ; Carrier to |P|)
    open Preorder R renaming (_∼_ to _∼ᵣ_ ; Carrier to |R|) 

Injective : ∀ {ℓA ℓA≈ ℓB ℓB≈} → (A : Setoid ℓA ℓA≈) → (B : Setoid ℓB ℓB≈) → (Setoid.Carrier A → Setoid.Carrier B) → 
        Set _
Injective {ℓA} {ℓA≈} {ℓB} {ℓB≈} A B f = ∀ {a a' : |A|} → (f a) B≈ (f a') → a A≈ a' 
  where
    |A| = Setoid.Carrier A
    |B| = Setoid.Carrier B
    _A≈_ = Setoid._≈_ A
    _B≈_ = Setoid._≈_ B 

-- the space of monotone functions from delta poset P to delta poset R 
_→+_ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} → Preorder ℓ₀ ℓ₁ ℓ₂ → Preorder ℓ₃ ℓ₄ ℓ₅ → Set _
P →+ R = P ⇒ R -- Σ[ f ∈ (|P| → |R|) ] Monotone P R f     
  where
    open Preorder P renaming (_∼_ to _∼ₚ_ ; Carrier to |P|)
    open Preorder R renaming (_∼_ to _∼ᵣ_ ; Carrier to |R|) 

-- the space of injective monotone functions (order embeddings) between preorders
_↣+_ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} → Preorder ℓ₀ ℓ₁ ℓ₂ → Preorder ℓ₃ ℓ₄ ℓ₅ → Set _
P ↣+ R = Σ[ |f| ∈ (|P| → |R|) ] Monotone P R |f| × Injective (preorder→setoid P) (preorder→setoid R) |f|
  where
    open Preorder P renaming (_∼_ to _∼ₚ_ ; Carrier to |P|)
    open Preorder R renaming (_∼_ to _∼ᵣ_ ; Carrier to |R|)

↣+-to-⇒ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} → {P : Preorder ℓ₀ ℓ₁ ℓ₂} → {Q : Preorder ℓ₃ ℓ₄ ℓ₅} →
            (P ↣+ Q) → (P ⇒ Q) 
↣+-to-⇒ {P} {Q} (f , mono , _) = record { fun = f ; monotone = mono }  

{- 
    P' : Setoid _ _
    P' = record
      { Carrier = Preorder.Carrier P
      ; _≈_ = Preorder._≈_ P
      ; isEquivalence = Preorder.isEquivalence P
      }

    R' : Setoid _ _
    R' = record
      { Carrier = Preorder.Carrier R
      ; _≈_ = Preorder._≈_ R
      ; isEquivalence = Preorder.isEquivalence R
      }
-}
-- the space of bounded join semilattice homomorphisms between bounded join semilattices S and T
_⇉_ : ∀ {c ℓ₁ ℓ₂ c' ℓ₁' ℓ₂'} → BoundedJoinSemilattice c ℓ₁ ℓ₂ → BoundedJoinSemilattice c' ℓ₁' ℓ₂' → Set (c ⊔ c' ⊔ ℓ₁ ⊔ ℓ₁')
S ⇉ T = Σ[ f ∈ (|S| → |T|)] (∀ (s1 s2 : |S|) → s1 ≈ₛ s2 → (f s1) ≈ₜ (f s2)) × (f ⊥ₛ ≈ₜ ⊥ₜ) × ∀ (s1 s2 : |S|) → f (s1 ∨ₛ s2) ≈ₜ (f s1) ∨ₜ (f s2) 
  where
    open BoundedJoinSemilattice S renaming (_≈_ to _≈ₛ_ ; ⊥ to ⊥ₛ ; _∨_ to _∨ₛ_ ; Carrier to |S|)
    open BoundedJoinSemilattice T renaming (_≈_ to _≈ₜ_ ; ⊥ to ⊥ₜ ; _∨_ to _∨ₜ_ ; Carrier to |T|)

-- the free semilattice functor's action on delta poset objects
FP : ∀{c ℓ⊑ ℓ< ℓ~} (P : DeltaPoset {c} {ℓ⊑} {ℓ<} {ℓ~}) → BoundedJoinSemilattice _ _ _
FP P = FP-BJS
  where
    open import FreeSemilattice.Semilattice P

⇉-mono : ∀ {c ℓ₁ ℓ₂ c' ℓ₁' ℓ₂'} → {S : BoundedJoinSemilattice c ℓ₁ ℓ₂} → {T : BoundedJoinSemilattice c' ℓ₁' ℓ₂'} → 
          (h : S ⇉ T) → {a b : BoundedJoinSemilattice.Carrier S} → (BoundedJoinSemilattice._≤_ S a b) → 
          (BoundedJoinSemilattice._≤_ T (proj₁ h $ a) (proj₁ h $ b))

⇉-mono {S = S} {T = T} h {a} {b} a≤b =
  begin
    (|h| a) ≈⟨ PT.Eq.sym $ P-BJT.identityʳ $ |h| a ⟩
    (|h| a) ∨T ⊥T ≤⟨ P-JT.∨-monotonic (PT.reflexive PT.Eq.refl) (BJT.minimum $ |h| b)  ⟩
    (|h| a) ∨T (|h| b) ≈⟨ PT.Eq.sym $ |h|-∨ a b ⟩
    (|h| $ a ∨S b) ≈⟨ |h|-≈ (a ∨S b) b $ connecting→ {A = jsS} a b a≤b ⟩
    (|h| b)
   ∎
  where
    jsS = BoundedJoinSemilattice.joinSemiLattice S
    jsT = BoundedJoinSemilattice.joinSemiLattice T

    open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset T)
    module BJT = BoundedJoinSemilattice T
    module PT = Poset (BoundedJoinSemilattice.poset T)

    open import Relation.Binary.Properties.BoundedJoinSemilattice T as P-BJT
    open import Relation.Binary.Properties.JoinSemilattice jsT as P-JT

    |h| = proj₁ h
    |h|-≈ = proj₁ $ proj₂ h
    |h|-∨ = proj₂ $ proj₂ $ proj₂ h

    _∨S_ = BoundedJoinSemilattice._∨_ S
    _∨T_ = BoundedJoinSemilattice._∨_ T
    ⊥S = BoundedJoinSemilattice.⊥ S
    ⊥T = BoundedJoinSemilattice.⊥ T
  

⇉-to-⇒ : ∀ {c ℓ₁ ℓ₂ c' ℓ₁' ℓ₂'} → {S : BoundedJoinSemilattice c ℓ₁ ℓ₂} → {T : BoundedJoinSemilattice c' ℓ₁' ℓ₂'} → 
          (h : S ⇉ T) → (BoundedJoinSemilattice.preorder S) ⇒ (BoundedJoinSemilattice.preorder T)
⇉-to-⇒ {S = S} {T = T} h = 
  record
  { fun = proj₁ h
  ; monotone = λ {x} {y} → ⇉-mono {S = S} {T = T} h {x} {y}
  }

♯ : (P : DeltaPoset {l0} {l0} {l0}) → (S : BoundedJoinSemilattice l0 l0 l0) → 
      _⇒_ {l0} {l0} (⇒-preorder (DeltaPoset.preorder P) (BoundedJoinSemilattice.preorder S))
      (⇒-preorder (BoundedJoinSemilattice.preorder (FP P))  (BoundedJoinSemilattice.preorder S))
♯ P S = 
  record
  { fun = fun
  ; monotone = λ {x} {y} → fun-mono {x} {y}
  }
  where
    open import Data.List renaming (map to mapList)
    open import Relation.Binary hiding (_⇒_)
    open import Relation.Binary.Lattice
    open import Relation.Binary.Properties.JoinSemilattice
    open import Relation.Binary.Properties.BoundedJoinSemilattice
    open DeltaPoset P renaming (Carrier to |P| ; _⊑_ to _⊑ₚ_ ; reflexive to ⊑ₚ-reflexive ; sym≈ to ≈ₚ-sym ; 
                                 refl≈ to ≈ₚ-refl ;  
                                 reflexive≈ to ≈ₚ-reflexive ; _≈_ to _≈ₚ_ ; ≈-setoid to ≈ₚ-setoid ;
                                 preorder to ⊑ₚ-preorder ; refl⊑ to ⊑ₚ-refl)
    open import FreeSemilattice P renaming (
      SemilatCarrier to |A| ; FP-BJS to A ; _≈_ to _≈ₐ_ ; _≤_ to _≤ₐ_ ; ⊥ to ⊥ₐ ; _∨_ to _∨ₐ_ ; ∨-assoc to ∨-assocₐ ;
      ∨-comm to ∨-commₐ ; FP-setoid to ≈ₐ-setoid ; ≈-refl to ≈ₐ-refl ; ≈-reflexive to ≈ₐ-reflexive ;
      preorder to ≤ₐ-preorder )
    open BoundedJoinSemilattice S renaming 
      (Carrier to |S| ; _≈_ to _≈ₛ_ ; refl to ≤ₛ-refl ; _≤_ to _≤ₛ_ ; reflexive to ≤ₛ-reflexive ; antisym to ≤ₛ-antisym ; 
       trans to ≤ₛ-trans ; preorder to ≤ₛ-preorder  ; 
       joinSemiLattice to joinSemilatticeₛ ; ⊥ to ⊥ₛ ; _∨_ to _∨ₛ_ ; poset to posetₛ )
    open BoundedJoinSemilattice.Eq S renaming (sym to ≈ₛ-sym ; refl to ≈ₛ-refl ; reflexive to ≈ₛ-reflexive)
    open import Data.List.Relation.Pointwise


    ≈ₛ-setoid : Setoid _ _
    ≈ₛ-setoid = preorder→setoid $ BoundedJoinSemilattice.preorder S

    fun-aux : (⊑ₚ-preorder ⇒ ≤ₛ-preorder) → (A ⇉ S)  
    --[[[
    fun-aux (record { fun = g ; monotone = g-mono }) =
      f , f-≈ , f-⊥ , f-∨
      where
        g-pres : g Preserves _≈ₚ_ ⟶ _≈ₛ_
        --[[[
        g-pres {p₁} {p₂} p₁≈p₂ = ≤ₛ-antisym (g-mono p₁⊑p₂) (g-mono p₂⊑p₁)
          where
            p₁⊑p₂ : p₁ ⊑ₚ p₂
            p₁⊑p₂ = ⊑ₚ-reflexive p₁≈p₂

            p₂⊑p₁ : p₂ ⊑ₚ p₁
            p₂⊑p₁ = ⊑ₚ-reflexive (≈ₚ-sym p₁≈p₂)
        --]]]
        f : |A| → |S|
        f (ds , f) = ∨-list {S} (mapList g ds)

        f-≈ : ∀ (a1 a2 : |A|) → a1 ≈ₐ a2 → (f a1) ≈ₛ (f a2)
        --[[[
        f-≈ ([] , f1) ([] , f2) a₁≈a₂ = BoundedJoinSemilattice.Eq.refl S
        f-≈ ([] , f1) (p₂ ∷ l₂ , f2) ()
        f-≈ (p₁ ∷ l₁ , f1) ([] , f2) ()
        f-≈ (p₁ ∷ l₁ , ∷-Free _ _ _ _ f₁') (p₂ ∷ l₂ , ∷-Free _ _ _ _ f₂') (p₁≈p₂ ∷ l₁≈l₂) =
          ≤ₛ-antisym (∨-monotonic joinSemilatticeₛ gp₁≤gp₂ $ ≤ₛ-reflexive r) 
                    (∨-monotonic joinSemilatticeₛ gp₂≤gp₁ $ ≤ₛ-reflexive $ BoundedJoinSemilattice.Eq.sym S r) 
          where
            gp₁≤gp₂ : g p₁ ≤ₛ g p₂
            gp₁≤gp₂ = g-mono (⊑ₚ-reflexive p₁≈p₂)

            gp₂≤gp₁ : g p₂ ≤ₛ g p₁
            gp₂≤gp₁ = g-mono (⊑ₚ-reflexive (≈ₚ-sym p₁≈p₂))

            r : f (l₁ , f₁') ≈ₛ f (l₂ , f₂')
            r = f-≈ (l₁ , f₁') (l₂ , f₂') l₁≈l₂  
        --]]]

        f-⊥ : (f ⊥ₐ) ≈ₛ ⊥ₛ
        f-⊥ = BoundedJoinSemilattice.Eq.refl S

        f-mono : ∀ {a₁ a₂ : |A|} → a₁ ≤ₐ a₂ → (f a₁) ≤ₛ (f a₂)
        --[[[
        f-mono {.[] , _} {a₂} [] = minimum (f a₂)
        f-mono {p₁ ∷ l₁ , ∷-Free _ _ _ _ f₁'} {a₂} (p₁≤a₂ ∷ l₁≤a₂) = 
          (proj₂ $ proj₂ $ supremum (g p₁) (f $ l₁ , f₁')) (f a₂) gp₁≤fa₂ fl₁≤fa₂  
          where
            fl₁≤fa₂ : (f $ l₁ , f₁') ≤ₛ (f a₂)
            fl₁≤fa₂ = f-mono {l₁ , f₁'} {a₂} l₁≤a₂

            gp₁≤fa₂ : (g p₁) ≤ₛ (f a₂)
            gp₁≤fa₂ = anyEliminate (proj₁ a₂) elim p₁≤a₂
              where
                elim : AnyEliminator {ℓQ = l0} |P| (g p₁ ≤ₛ f a₂) (p₁ ⊑ₚ_) (proj₁ a₂)
                elim z _ p₁⊑z z∈a₂ = ≤ₛ-trans (g-mono p₁⊑z) gz≤fa₂
                  where
                    open import Data.List.Membership.Propositional.Properties
                    gz≤fa₂ : (g z) ≤ₛ (f a₂)
                    gz≤fa₂ = LA.lookup {A = |S|} {P = _≤ₛ (f a₂)} 
                                       (∨-list-upper {S} (mapList g (proj₁ a₂))) 
                                       (∈-map⁺ z∈a₂)
        --]]]

        f-∨ : ∀ (a₁ a₂ : |A|) → f (a₁ ∨ₐ a₂) ≈ₛ (f a₁) ∨ₛ (f a₂)
        --[[[
        f-∨ a₁ a₂ = ≤ₛ-antisym f-a₁∨a₂≤fa₁∨fa₂ fa₁∨fa₂≤f-a₁∨a₂
          where
            f-a₁∨a₂≤fa₁∨fa₂ : f (a₁ ∨ₐ a₂) ≤ₛ (f a₁) ∨ₛ (f a₂)
            --[[[
            f-a₁∨a₂≤fa₁∨fa₂ = 
              begin
                f (a₁ ∨ₐ a₂) 
                  ≤⟨ ∨-list-≤ {S} (mapList g (proj₁ $ a₁ ∨ₐ a₂)) ((f a₁) ∷ (f a₂) ∷ []) p ⟩ 
                ∨-list {S} ((f a₁) ∷ (f a₂) ∷ []) 
                  ≈⟨ ≈ₛ-sym $ ∨-to-list {S} (f a₁) (f a₂) ⟩ 
                (f a₁) ∨ₛ (f a₂)
               ∎
              where
                open import Relation.Binary.Lattice
                open import Relation.Binary.PartialOrderReasoning (BoundedJoinSemilattice.poset S)
                open import Data.List.Membership.Setoid.Properties

                open import Data.List.Membership.Setoid ≈ₛ-setoid renaming (_∈_ to _∈ₛ_)

                q : {v : |S|} → (v ∈≡ (mapList g (proj₁ (a₁ ∨ₐ a₂)))) → Any (v ≤ₛ_) (f a₁ ∷ f a₂ ∷ [])
                --[[[
                q {v} v∈≡g-a₁∨a₂ with ∈-map⁻ ≈ₚ-setoid ≈ₛ-setoid (LAny.map ≈ₛ-reflexive v∈≡g-a₁∨a₂)
                q {v} v∈≡g-a₁∨a₂ | (p , p∈a₁∨a₂ , v≡gp) with (to ⟨$⟩ p∈a₁∨a₂)
                  where
                    open Equivalence (x∈∨⇔P∨ a₁ a₂ (a₁ ∨ₐ a₂) (≈ₐ-refl {a₁ ∨ₐ a₂}) p)
                q {v} v∈≡g-a₁∨a₂ | p , p∈a₁∨a₂ , v≈gp | inj₁ (p∈a₁ , ¬p⊑a₂) =
                  here (Preorder.∼-respˡ-≈ ≤ₛ-preorder (≈ₛ-sym v≈gp) gp≤fa₁)
                  where
                    gp∈ga₁ : (g p) ∈ₛ (mapList g $ proj₁ a₁)
                    gp∈ga₁ = ∈-map⁺ ≈ₚ-setoid ≈ₛ-setoid {f = g} g-pres p∈a₁

                    gp≤ga₁ : Any ((g p) ≤ₛ_) (mapList g $ proj₁ a₁)
                    gp≤ga₁ = LAny.map ≤ₛ-reflexive gp∈ga₁

                    gp≤fa₁ : (g p) ≤ₛ (f a₁) 
                    gp≤fa₁ = anyEliminate (mapList g $ proj₁ a₁) elim gp≤ga₁
                      where
                        elim : AnyEliminator {ℓQ = l0} |S| ((g p) ≤ₛ (f a₁)) ((g p) ≤ₛ_) (mapList g $ proj₁ a₁)
                        elim z f gp≤z z∈≡ga₁ = ≤ₛ-trans gp≤z (LA.lookup (∨-list-upper {S} (mapList g $ proj₁ a₁)) z∈≡ga₁)

                q {v} v∈≡g-a₁∨a₂ | p , p∈a₁∨a₂ , v≈gp | inj₂ (inj₁ (p∈a₂ , ¬p⊑a₁)) = 
                  there $ here (Preorder.∼-respˡ-≈ ≤ₛ-preorder (≈ₛ-sym v≈gp) gp≤fa₂)
                  where
                    gp∈ga₂ : (g p) ∈ₛ (mapList g $ proj₁ a₂)
                    gp∈ga₂ = ∈-map⁺ ≈ₚ-setoid ≈ₛ-setoid {f = g} g-pres p∈a₂

                    gp≤ga₂ : Any ((g p) ≤ₛ_) (mapList g $ proj₁ a₂)
                    gp≤ga₂ = LAny.map ≤ₛ-reflexive gp∈ga₂

                    gp≤fa₂ : (g p) ≤ₛ (f a₂) 
                    gp≤fa₂ = anyEliminate (mapList g $ proj₁ a₂) elim gp≤ga₂
                      where
                        elim : AnyEliminator {ℓQ = l0} |S| ((g p) ≤ₛ (f a₂)) ((g p) ≤ₛ_) (mapList g $ proj₁ a₂)
                        elim z f gp≤z z∈≡ga₂ = ≤ₛ-trans gp≤z (LA.lookup (∨-list-upper {S} (mapList g $ proj₁ a₂)) z∈≡ga₂)
                q {v} v∈≡g-a₁∨a₂ | p , p∈a₁∨a₂ , v≈gp | inj₂ (inj₂ (p∈a₁ , p∈a₂)) =
                  here (Preorder.∼-respˡ-≈ ≤ₛ-preorder (≈ₛ-sym v≈gp) gp≤fa₁)
                  where
                    gp∈ga₁ : (g p) ∈ₛ (mapList g $ proj₁ a₁)
                    gp∈ga₁ = ∈-map⁺ ≈ₚ-setoid ≈ₛ-setoid {f = g} g-pres p∈a₁

                    gp≤ga₁ : Any ((g p) ≤ₛ_) (mapList g $ proj₁ a₁)
                    gp≤ga₁ = LAny.map ≤ₛ-reflexive gp∈ga₁

                    gp≤fa₁ : (g p) ≤ₛ (f a₁) 
                    gp≤fa₁ = anyEliminate (mapList g $ proj₁ a₁) elim gp≤ga₁
                      where
                        elim : AnyEliminator {ℓQ = l0} |S| ((g p) ≤ₛ (f a₁)) ((g p) ≤ₛ_) (mapList g $ proj₁ a₁)
                        elim z f gp≤z z∈≡ga₁ = ≤ₛ-trans gp≤z (LA.lookup (∨-list-upper {S} (mapList g $ proj₁ a₁)) z∈≡ga₁)
            --]]]

                p : All (λ · → Any (_≤ₛ_ ·) (f a₁ ∷ f a₂ ∷ [])) (mapList g (proj₁ (a₁ ∨ₐ a₂)))
                p = LA.tabulate q  
            --]]]

            fa₁∨fa₂≤f-a₁∨a₂ : (f a₁) ∨ₛ (f a₂) ≤ₛ f (a₁ ∨ₐ a₂)
            --[[[

            fa₁∨fa₂≤f-a₁∨a₂ = (proj₂ $ proj₂ $ supremum (f a₁) (f a₂)) (f $ a₁ ∨ₐ a₂) f-a₁≤f-a₁∨a₂ f-a₂≤f-a₁∨a₂
              where
                open BoundedJoinSemilattice A renaming (supremum to sup) 
                f-a₁≤f-a₁∨a₂ : (f a₁) ≤ₛ (f $ a₁ ∨ₐ a₂)
                f-a₁≤f-a₁∨a₂ = f-mono {a₁} {a₁ ∨ₐ a₂} (proj₁ $ sup a₁ a₂)

                f-a₂≤f-a₁∨a₂ : (f a₂) ≤ₛ (f $ a₁ ∨ₐ a₂)
                f-a₂≤f-a₁∨a₂ = f-mono {a₂} {a₁ ∨ₐ a₂} (proj₁ $ proj₂ $ sup a₁ a₂)

            --]]]
          --]]]
      --]]]

    fun : (⊑ₚ-preorder ⇒ ≤ₛ-preorder) → (≤ₐ-preorder ⇒ ≤ₛ-preorder)
    --[[[
    fun x = 
      record
      { fun = proj₁ hom
      ; monotone = λ {x} {y} → ⇉-mono {S = A} {T = S} hom {x} {y}
      }
      where
        hom = fun-aux x
    --]]]
        
    fun-mono : (Preorder._∼_ $ ⇒-preorder ⊑ₚ-preorder ≤ₛ-preorder) 
               =[ fun ]⇒ 
               (Preorder._∼_ $ ⇒-preorder ≤ₐ-preorder ≤ₛ-preorder)
    --[[[
    fun-mono {f₁} {f₂} f₁≤f₂ {a} = 
      begin
        |h₁| a 
          ≡⟨ PE.refl ⟩
        (∨-list {S} $ mapList |f₁| $ proj₁ a)
          ∼⟨ ∨-list-pointwise-≤ (mapList |f₁| $ proj₁ a) (mapList |f₂| $ proj₁ a) (aux $ proj₁ a) ⟩ 
        (∨-list {S} $ mapList |f₂| $ proj₁ a)
          ≡⟨ PE.refl ⟩ 
        |h₂| a
       ∎ 
      where
        open import Relation.Binary.PreorderReasoning ≤ₛ-preorder
        open import Data.List.Relation.Pointwise as LPW

        |f₁| = _⇒_.fun f₁
        f₁-mono = _⇒_.monotone f₁

        |f₂| = _⇒_.fun f₂
        f₂-mono = _⇒_.monotone f₂

        h₁ = fun f₁
        |h₁| = _⇒_.fun h₁
        h₁-monotone = _⇒_.monotone h₁  
        h₁-≈ = let _ , h₁-≈ , _ , _ = fun-aux f₁ in h₁-≈ 

        h₂ = fun f₂
        |h₂| = _⇒_.fun h₂
        h₂-monotone = _⇒_.monotone h₂  
        h₂-≈ = let _ , h₁-≈ , _ , _ = fun-aux f₁ in h₁-≈ 

        aux : (x : List |P|) → Pointwise _≤ₛ_ (mapList |f₁| $ x) (mapList |f₂| $ x)
        aux [] = []
        aux (p ∷ l) = (f₁≤f₂ {p}) ∷ (aux l)
    --]]]


{-
⇉-resp-≈ : ∀ {c ℓ₁ ℓ₂ c' ℓ₁' ℓ₂'} → {S : BoundedJoinSemilattice c ℓ₁ ℓ₂} → {T : BoundedJoinSemilattice c' ℓ₁' ℓ₂'} →
            (h : S ⇉ T) → (s1 s2 : BoundedJoinSemilattice.Carrier S) → (BoundedJoinSemilattice._≈_ S s1 s2) → 
            (BoundedJoinSemilattice._≈_ T (proj₁ h $ s1) (proj₁ h $ s2))

⇉-resp-≈ {S = S} {T} (|h| , |h|-⊥ , |h|-∨) s1 s2 s1≈s2 = 
  begin
    |h| s1 ≈⟨   ⟩    
   ∎ 
  where
    module S' = BoundedJoinSemilattice S
    module T' = BoundedJoinSemilattice T

    ≈-setoid : Setoid _ _
    ≈-setoid = record
      { Carrier = T'.Carrier
      ; isEquivalence = T'.isEquivalence 
      }

    open import Relation.Binary.EqReasoning ≈-setoid

    s1≤s2 : s1 S'.≤ s2 
    s1≤s2 = S'.reflexive s1≈s2

    s2≤s1 : s2 S'.≤ s1 
    s2≤s1 = S'.reflexive (S'.Eq.sym s1≈s2)

    s2∨s1≈s1 : s2 S'.∨ s1 S'.≈ s1 
    s2∨s1≈s1 = connecting→ {A = S'.joinSemiLattice} s2 s1 s2≤s1

    s1∨s2≈s2 : s1 S'.∨ s2 S'.≈ s2 
    s1∨s2≈s2 = connecting→ {A = S'.joinSemiLattice} s1 s2 s1≤s2
-}



{-
Ff : (P R : DeltaPoset0) → (f : P →+ R) → (FP P) ⇉ (FP R)
Ff P R (f , f+) = |Ff| , hom⊥ , hom∨   
  where
    open DeltaPoset0 R renaming (_⊑_ to _⊑ᵣ_ ; _<_ to _<ᵣ_ ; Carrier to |R|)
    module DP-P = DeltaPoset0 P 
    open DeltaPoset0 P renaming (_⊑_ to _⊑ₚ_ ; _<_ to _<ₚ_  ; Carrier to |P|)
    module FP-P = BoundedJoinSemilattice (FP P) 
    open BoundedJoinSemilattice (FP P) 
      renaming (_≈_ to _≈ₚ_ ; ⊥ to ⊥ₚ ; _∨_ to _∨ₚ_ ; Carrier to |FP| ; _≤_ to _≤ₚ_)
    module FP-R = BoundedJoinSemilattice (FP R)
    open BoundedJoinSemilattice (FP R) 
      renaming (_≈_ to _≈ᵣ_ ; ⊥ to ⊥ᵣ ; _∨_ to _∨ᵣ_ ; Carrier to |FR| ; _≤_ to _≤ᵣ_)
    open import FreeSemilattice.Semilattice P as FS-P 
    open import FreeSemilattice.Semilattice R as FS-R
    -- renaming _∨_ makes the goal output much easier to read
    open import FreeSemilattice.Core P 
      renaming ([]-Free to []-Freeₚ ; ∷-Free to ∷-Freeₚ ; _∨_ to _⊔ₚ_ ; ∨-free to ∨-freeₚ)
    open import FreeSemilattice.Core R 
      renaming ([]-Free to []-Freeᵣ ; ∷-Free to ∷-Freeᵣ ; _∨_ to _⊔ᵣ_ ; ∨-free to ∨-freeᵣ ;
                a∨b≈b⇔a≤b to a∨b≈b⇔a≤bᵣ)

    open import Relation.Binary.Properties.JoinSemilattice FP-P.joinSemiLattice 
      renaming (∨-comm to ∨-commₚ ; ∨-assoc to ∨-assocₚ ; ∨-idempotent to ∨-idemₚ ) 

    open import Relation.Binary.Properties.JoinSemilattice FP-R.joinSemiLattice 
      renaming (∨-comm to ∨-commᵣ ; ∨-assoc to ∨-assocᵣ ; ∨-idempotent to ∨-idemᵣ )

    ηₚ = η P
    ηᵣ = η R

    |Ff| : |FP| → |FR|
    |Ff| ([] , []-Freeₚ) = [] , []-Freeᵣ
    |Ff| ((hp ∷ tp) , ∷-Freeₚ _ _ _ _ ftp) = 
      let
        hr : |R|
        hr = f hp

        tr : |FR|
        tr = |Ff| (tp , ftp)
      in
      (ηᵣ hr) ∨ᵣ tr 

    hom⊥ : (|Ff| ⊥ₚ ≈ᵣ ⊥ᵣ)
    hom⊥ = PE.refl

    hom∨ : (p1 p2 : |FP|) → (|Ff| $ p1 ∨ₚ p2) ≈ᵣ (|Ff| p1) ∨ᵣ (|Ff| p2)
    hom∨ ([] , []-Freeₚ) (p2 , f2) rewrite hom⊥ = PE.refl
    hom∨ (h1 ∷ t1 , ∷-Freeₚ _ _ min1 incomp1 ft1) ([] , []-Freeₚ) =
      PE.sym $ FS-R.∨'-unitʳ ((ηᵣ $ f h1) ∨ᵣ (|Ff| $ t1 , ft1))
    hom∨ (h1 ∷ t1 , ∷-Freeₚ _ _ _ _ _) (h2 ∷ t2 , ∷-Freeₚ _ _ _ _ _) with h1 DP-P.∦? h2 
    hom∨ (h1 ∷ t1 , ∷-Freeₚ _ _ _ _ ft1) (l2@(h2 ∷ t2) , f2@(∷-Freeₚ _ _ _ _ ft2)) | DP-P.l⊑r h1⊑h2 ¬h2⊑h1 = 
      PE.sym $
      begin
        (π₁ (ηᵣ h1') ⊔ᵣ π₁ t1') ⊔ᵣ (π₁ (ηᵣ h2' ) ⊔ᵣ π₁ t2') 
          ≡⟨ PE.cong (λ x → x ⊔ᵣ (π₁ (ηᵣ h2') ⊔ᵣ π₁ t2')) $ ∨-commᵣ (ηᵣ h1') t1'   ⟩ 
        (π₁ t1' ⊔ᵣ π₁ (ηᵣ h1')) ⊔ᵣ (π₁ (ηᵣ h2' ) ⊔ᵣ π₁ t2') 
          ≡⟨ PE.sym $ ∨-assocᵣ (t1' ∨ᵣ (ηᵣ h1')) (ηᵣ h2') t2' ⟩
        ((π₁ t1' ⊔ᵣ π₁ (ηᵣ h1')) ⊔ᵣ π₁ (ηᵣ h2')) ⊔ᵣ π₁ t2' 
          ≡⟨ PE.cong (λ x → x ⊔ᵣ (π₁ t2')) $ ∨-assocᵣ t1' (ηᵣ h1') (ηᵣ h2') ⟩
        (π₁ t1' ⊔ᵣ (π₁ (ηᵣ h1') ⊔ᵣ π₁ (ηᵣ h2'))) ⊔ᵣ π₁ t2' 
          ≡⟨ PE.cong (λ x → (π₁ t1' ⊔ᵣ x) ⊔ᵣ (π₁ t2')) $ η1∨η2≡η2 ⟩
        (π₁ t1' ⊔ᵣ π₁ (ηᵣ h2')) ⊔ᵣ π₁ t2' 
          ≡⟨ ∨-assocᵣ t1' (ηᵣ h2') t2' ⟩
        π₁ t1' ⊔ᵣ (π₁ (ηᵣ h2') ⊔ᵣ π₁ t2') 
          ≡⟨ PE.sym $ hom∨ (t1 , ft1) (h2 ∷ t2 , f2) ⟩
        π₁ (|Ff| $ t1 ⊔ₚ (h2 ∷ t2) , ∨-freeₚ ft1 f2)
       ∎
      where
        open PE.≡-Reasoning
        
        π₁ = proj₁
        π₂ = proj₂

        h1' = f h1
        h2' = f h2

        t1' = |Ff| (t1 , ft1)
        t2' = |Ff| (t2 , ft2)
        
        h1'⊑h2' : h1' ⊑ᵣ h2'
        h1'⊑h2' = f+ h1⊑h2

        η1≤η2 : (ηᵣ h1') ≤ᵣ (ηᵣ h2')
        η1≤η2 = (here h1'⊑h2') ∷ []

        η1∨η2≡η2 : (ηᵣ h1') ∨ᵣ (ηᵣ h2') ≈ᵣ (ηᵣ h2')
        η1∨η2≡η2 = from ⟨$⟩ η1≤η2
          where
            open Equivalence (a∨b≈b⇔a≤bᵣ (ηᵣ h1') (ηᵣ h2'))

    hom∨ (h1 ∷ t1 , f1@(∷-Freeₚ _ _ _ _ ft1)) (l2@(h2 ∷ t2) , ∷-Freeₚ _ _ _ _ ft2) | DP-P.r⊑l ¬h1⊑h2 h2⊑h1 =     
      PE.sym $
      begin
        (π₁ (ηᵣ h1') ⊔ᵣ π₁ t1') ⊔ᵣ π₁ (ηᵣ h2') ⊔ᵣ π₁ t2' 
          ≡⟨ PE.sym $ ∨-assocᵣ ((ηᵣ h1') ∨ᵣ t1') (ηᵣ h2') t2' ⟩
        ((π₁ (ηᵣ h1') ⊔ᵣ π₁ t1') ⊔ᵣ π₁ (ηᵣ h2')) ⊔ᵣ π₁ t2'
          ≡⟨ PE.cong (λ x → x ⊔ᵣ π₁ t2') $ ∨-assocᵣ (ηᵣ h1') t1' (ηᵣ h2') ⟩
        (π₁ (ηᵣ h1') ⊔ᵣ (π₁ t1' ⊔ᵣ π₁ (ηᵣ h2'))) ⊔ᵣ π₁ t2' 
          ≡⟨ PE.cong (λ x → (π₁ (ηᵣ h1') ⊔ᵣ x) ⊔ᵣ π₁ t2') $ ∨-commᵣ t1' (ηᵣ h2') ⟩
        (π₁ (ηᵣ h1') ⊔ᵣ (π₁ (ηᵣ h2') ⊔ᵣ π₁ t1')) ⊔ᵣ π₁ t2' 
          ≡⟨ PE.cong (λ x → x ⊔ᵣ π₁ t2') $ PE.sym (∨-assocᵣ (ηᵣ h1') (ηᵣ h2') t1')  ⟩ 
        ((π₁ (ηᵣ h1') ⊔ᵣ π₁ (ηᵣ h2')) ⊔ᵣ π₁ t1') ⊔ᵣ π₁ t2' 
          ≡⟨ PE.cong (λ x → (x ⊔ᵣ π₁ t1') ⊔ᵣ π₁ t2') $ ∨-commᵣ (ηᵣ h1') (ηᵣ h2') ⟩
        ((π₁ (ηᵣ h2') ⊔ᵣ π₁ (ηᵣ h1')) ⊔ᵣ π₁ t1') ⊔ᵣ π₁ t2' 
          ≡⟨ PE.cong (λ x → (x ⊔ᵣ π₁ t1') ⊔ᵣ π₁ t2') $ η2∨η1≡η1 ⟩ 
        (π₁ (ηᵣ h1') ⊔ᵣ π₁ t1') ⊔ᵣ π₁ t2'  
          ≡⟨ PE.sym $ hom∨ (h1 ∷ t1 , f1) (t2 , ft2) ⟩
        π₁ (|Ff| $ (h1 ∷ t1) ⊔ₚ t2 , ∨-freeₚ f1 ft2)
       ∎
      where
        open PE.≡-Reasoning

        π₁ = proj₁
        π₂ = proj₂

        h1' = f h1
        h2' = f h2

        t1' = |Ff| (t1 , ft1)
        t2' = |Ff| (t2 , ft2)
        
        h2'⊑h1' : h2' ⊑ᵣ h1'
        h2'⊑h1' = f+ h2⊑h1      

        η2≤η1 : (ηᵣ h2') ≤ᵣ (ηᵣ h1')
        η2≤η1 = (here h2'⊑h1') ∷ []

        η2∨η1≡η1 : (ηᵣ h2') ∨ᵣ (ηᵣ h1') ≈ᵣ (ηᵣ h1')
        η2∨η1≡η1 = from ⟨$⟩ η2≤η1
          where
            open Equivalence (a∨b≈b⇔a≤bᵣ (ηᵣ h2') (ηᵣ h1'))

    hom∨ (h1 ∷ t1 , f1@(∷-Freeₚ _ _ _ _ ft1)) (l2@(h2 ∷ t2) , f2@(∷-Freeₚ _ _ _ _ ft2)) | DP-P.l≡r h1≡h2 =
      PE.sym $
      begin
        (π₁ (ηᵣ h1') ⊔ᵣ π₁ t1') ⊔ᵣ (π₁ (ηᵣ h2' ) ⊔ᵣ π₁ t2') 
          ≡⟨ PE.cong (λ x → x ⊔ᵣ (π₁ (ηᵣ h2') ⊔ᵣ π₁ t2')) $ ∨-commᵣ (ηᵣ h1') t1'   ⟩ 
        (π₁ t1' ⊔ᵣ π₁ (ηᵣ h1')) ⊔ᵣ (π₁ (ηᵣ h2' ) ⊔ᵣ π₁ t2') 
          ≡⟨ PE.sym $ ∨-assocᵣ (t1' ∨ᵣ (ηᵣ h1')) (ηᵣ h2') t2' ⟩
        ((π₁ t1' ⊔ᵣ π₁ (ηᵣ h1')) ⊔ᵣ π₁ (ηᵣ h2')) ⊔ᵣ π₁ t2' 
          ≡⟨ PE.cong (λ x → x ⊔ᵣ (π₁ t2')) $ ∨-assocᵣ t1' (ηᵣ h1') (ηᵣ h2') ⟩
        (π₁ t1' ⊔ᵣ (π₁ (ηᵣ h1') ⊔ᵣ π₁ (ηᵣ h2'))) ⊔ᵣ π₁ t2' 
          ≡⟨ PE.cong (λ x → (π₁ t1' ⊔ᵣ x) ⊔ᵣ (π₁ t2')) $ η1∨η2≡η2 ⟩
        (π₁ t1' ⊔ᵣ π₁ (ηᵣ h2')) ⊔ᵣ π₁ t2' 
          ≡⟨ ∨-assocᵣ t1' (ηᵣ h2') t2' ⟩
        π₁ t1' ⊔ᵣ (π₁ (ηᵣ h2') ⊔ᵣ π₁ t2') 
          ≡⟨ PE.sym $ hom∨ (t1 , ft1) (h2 ∷ t2 , f2) ⟩
        π₁ (|Ff| $ t1 ⊔ₚ (h2 ∷ t2) , ∨-freeₚ ft1 f2)
       ∎
      where
        open PE.≡-Reasoning
        
        π₁ = proj₁
        π₂ = proj₂

        h1' = f h1
        h2' = f h2

        t1' = |Ff| (t1 , ft1)
        t2' = |Ff| (t2 , ft2)
        
        h1'⊑h2' : h1' ⊑ᵣ h2'
        h1'⊑h2' = f+ (DeltaPoset0.reflexive P h1≡h2)

        η1≤η2 : (ηᵣ h1') ≤ᵣ (ηᵣ h2')
        η1≤η2 = (here h1'⊑h2') ∷ []

        η1∨η2≡η2 : (ηᵣ h1') ∨ᵣ (ηᵣ h2') ≈ᵣ (ηᵣ h2')
        η1∨η2≡η2 = from ⟨$⟩ η1≤η2
          where
            open Equivalence (a∨b≈b⇔a≤bᵣ (ηᵣ h1') (ηᵣ h2'))

    hom∨ (h1 ∷ t1 , f1) (l2@(h2 ∷ t2) , f2) | DP-P.l∥r h1∥h2 with DeltaPoset0.compare P h1 h2
    hom∨ (h1 ∷ t1 , f1@(∷-Freeₚ _ _ _ _ ft1) ) (l2@(h2 ∷ t2) , f2@(∷-Freeₚ _ _ _ _ ft2)) | DP-P.l∥r h1∥h2 | tri< h1<h2 _ _ = 
      PE.sym $
      begin
        (π₁ ηh1' ⊔ᵣ π₁ t1') ⊔ᵣ (π₁ ηh2' ⊔ᵣ π₁ t2')
          ≡⟨ ∨-assocᵣ ηh1' t1' (ηh2' ∨ᵣ t2') ⟩
        (π₁ ηh1') ⊔ᵣ (π₁ t1' ⊔ᵣ (π₁ ηh2' ⊔ᵣ π₁ t2'))  
          ≡⟨ PE.cong (λ x → (π₁ ηh1') ⊔ᵣ x) $ PE.sym $ hom∨ (t1 , ft1) (h2 ∷ t2 , f2)   ⟩ 
        π₁ ηh1' ⊔ᵣ proj₁ (|Ff| (t1 ⊔ₚ (h2 ∷ t2) , ∨-freeₚ ft1 f2))
       ∎
      where
        open PE.≡-Reasoning

        π₁ = proj₁
        π₂ = proj₂

        ηh1' = ηᵣ $ f h1
        ηh2' = ηᵣ $ f h2

        t1' = |Ff| (t1 , ft1)
        t2' = |Ff| (t2 , ft2)
    hom∨ (h1 ∷ t1 , f1) (l2@(h2 ∷ t2) , f2) | DP-P.l∥r h1∥h2 | tri≈ _ h1≡h2 _ = 
      ⊥-elim $ h1∥h2 (inj₁ $ DeltaPoset0.reflexive P h1≡h2) 
    hom∨ (h1 ∷ t1 , f1@(∷-Freeₚ _ _ _ _ ft1)) (l2@(h2 ∷ t2) , f2@(∷-Freeₚ _ _ _ _ ft2)) | DP-P.l∥r h1∥h2 | tri> _ _ h2<h1 = 
      PE.sym $
      begin
        (π₁ ηh1' ⊔ᵣ π₁ t1') ⊔ᵣ (π₁ ηh2' ⊔ᵣ π₁ t2')
          ≡⟨ ∨-assocᵣ ηh1' t1' (ηh2' ∨ᵣ t2') ⟩
        (π₁ ηh1') ⊔ᵣ (π₁ t1' ⊔ᵣ (π₁ ηh2' ⊔ᵣ π₁ t2'))
          ≡⟨ PE.cong (λ x → (π₁ ηh1') ⊔ᵣ x) $ PE.sym $ ∨-assocᵣ t1' ηh2' t2' ⟩
        (π₁ ηh1') ⊔ᵣ ((π₁ t1' ⊔ᵣ π₁ ηh2') ⊔ᵣ π₁ t2')
          ≡⟨ PE.cong (λ x → (π₁ ηh1') ⊔ᵣ (x ⊔ᵣ (π₁ t2'))) $ ∨-commᵣ t1' ηh2' ⟩
        (π₁ ηh1') ⊔ᵣ ((π₁ ηh2' ⊔ᵣ π₁ t1') ⊔ᵣ π₁ t2')
          ≡⟨ PE.sym $ ∨-assocᵣ ηh1' (ηh2' ∨ᵣ t1') t2' ⟩ 
        ((π₁ ηh1') ⊔ᵣ ((π₁ ηh2') ⊔ᵣ (π₁ t1'))) ⊔ᵣ (π₁ t2')
          ≡⟨ PE.cong (λ x → x ⊔ᵣ (π₁ t2')) $ PE.sym $ ∨-assocᵣ ηh1' ηh2' t1' ⟩
        (((π₁ ηh1') ⊔ᵣ (π₁ ηh2')) ⊔ᵣ (π₁ t1')) ⊔ᵣ (π₁ t2')
          ≡⟨ PE.cong (λ x → (x ⊔ᵣ π₁ t1') ⊔ᵣ π₁ t2') $ ∨-commᵣ ηh1' ηh2' ⟩
        (((π₁ ηh2') ⊔ᵣ (π₁ ηh1')) ⊔ᵣ (π₁ t1')) ⊔ᵣ (π₁ t2')
          ≡⟨ PE.cong (λ x → x ⊔ᵣ (π₁ t2')) $ ∨-assocᵣ ηh2' ηh1' t1' ⟩
        ((π₁ ηh2') ⊔ᵣ ((π₁ ηh1') ⊔ᵣ (π₁ t1'))) ⊔ᵣ (π₁ t2')
          ≡⟨ ∨-assocᵣ ηh2' (ηh1' ∨ᵣ t1') t2' ⟩ 
        (π₁ ηh2') ⊔ᵣ (((π₁ ηh1') ⊔ᵣ (π₁ t1')) ⊔ᵣ (π₁ t2'))
          ≡⟨ PE.cong (λ x → (π₁ ηh2') ⊔ᵣ x) $ PE.sym $ hom∨ (h1 ∷ t1 , f1) (t2 , ft2)  ⟩ 
        (π₁ ηh2') ⊔ᵣ (π₁ (|Ff| ((h1 ∷ t1) ⊔ₚ t2 , ∨-freeₚ f1 ft2)))    
       ∎
      where
        open PE.≡-Reasoning

        π₁ = proj₁
        π₂ = proj₂

        ηh1' = ηᵣ $ f h1
        ηh2' = ηᵣ $ f h2

        t1' = |Ff| (t1 , ft1)
        t2' = |Ff| (t2 , ft2)
-}
