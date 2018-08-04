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


module FreeSemilattice where

BoundedJoinSemilattice0 : Set₂
BoundedJoinSemilattice0 = BoundedJoinSemilattice l1 l0 l0

-- the space of monotone functions between delta posets P and R 
_→+_ : DeltaPoset0 → DeltaPoset0 → Set
P →+ R = Σ[ f ∈ (|P| → |R|) ] ∀ {p1 p2 : |P|} → p1 ⊑ₚ p2 → f p1 ⊑ᵣ f p2     
  where
    open DeltaPoset0 P renaming (_⊑_ to _⊑ₚ_ ; Carrier to |P|)
    open DeltaPoset0 R renaming (_⊑_ to _⊑ᵣ_ ; Carrier to |R|) 

-- the space of bounded join semilattice homomorphisms between bounded join semilattices S and T
_⇉_ : BoundedJoinSemilattice0 → BoundedJoinSemilattice0 → Set₁
S ⇉ T = Σ[ f ∈ (|S| → |T|)] (f ⊥ₛ ≡ ⊥ₜ) × ∀ (s1 s2 : |S|) → f (s1 ∨ₛ s2) ≈ₜ (f s1) ∨ₜ (f s2) 
  where
    open BoundedJoinSemilattice S renaming (⊥ to ⊥ₛ ; _∨_ to _∨ₛ_ ; Carrier to |S|)
    open BoundedJoinSemilattice T renaming (_≈_ to _≈ₜ_ ; ⊥ to ⊥ₜ ; _∨_ to _∨ₜ_ ; Carrier to |T|)

-- the free semilattice functor's action on delta poset objects
FP : (P : DeltaPoset0) → BoundedJoinSemilattice0
FP P = FP-BJS
  where
    open import FreeSemilattice.Semilattice P

Ff : (P R : DeltaPoset0) → (f : P →+ R) → (FP P) ⇉ (FP R)
Ff P R (f , f+) = {!!}   
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
    open import FreeSemilattice.Semilattice P as FS-P renaming (η to ηₚ ; ↓ to ↓ₚ)
    open import FreeSemilattice.Semilattice R as FS-R renaming (η to ηᵣ ; ↓ to ↓ᵣ)
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
    hom∨ (h1 ∷ t1 , f1) (l2@(h2 ∷ t2) , f2) | DP-P.l∥r h1∥h2 | tri< h1<h2 _ _ = 
      ?
    hom∨ (h1 ∷ t1 , f1) (l2@(h2 ∷ t2) , f2) | DP-P.l∥r h1∥h2 | tri≈ _ h1≡h2 _ = 
      ?
    hom∨ (h1 ∷ t1 , f1) (l2@(h2 ∷ t2) , f2) | DP-P.l∥r h1∥h2 | tri> _ _ h2<h1 = 
      ?
