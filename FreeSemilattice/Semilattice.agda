open import Function using (_$_)
open import Function.Equivalence as FE
open import Function.Equality using (_⟨$⟩_)
open import Data.Empty
open import Data.List
open import Data.List.All as LA
open import Data.List.Any as LAny
open import Data.List.Any.Properties as LAP
open import Data.List.Relation.Pointwise as PW hiding (Rel ; transitive ; reflexive)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_) 
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE
open import Deltas
open import Util

module FreeSemilattice.Semilattice {c ℓ⊑ ℓ< ℓ≈} (P : DeltaPoset {c} {ℓ⊑} {ℓ<} {ℓ≈}) where

open import FreeSemilattice.Core P
open import FreeSemilattice.Poset P as PS

open DeltaPoset P renaming (_≈_ to _~_ ; trans≈ to trans~ ; sym≈ to sym~ ; refl≈ to refl~ ;
  ∦-respʳ-≈ to ∦-respʳ-~ ; ∦-respˡ-≈ to ∦-respˡ-~ ;
  ∥-respʳ-≈ to ∥-respʳ-~ ; ∥-respˡ-≈ to ∥-respˡ-~ ;
  <-respʳ-≈ to <-respʳ-~ ; <-respˡ-≈ to <-respˡ-~ ; 
  ⊑-respʳ-≈ to ⊑-respʳ-~ ; ⊑-respˡ-≈ to ⊑-respˡ-~ ;
  ≈-decSetoid to ~-decSetoid ; _≈?_ to _~?_)

open import Data.List.Membership.DecSetoid ~-decSetoid

∨-unitʳ : (l : List Carrier) → l ∨ [] ≡ l
∨-unitʳ [] = PE.refl
∨-unitʳ (x ∷ l) = PE.refl

∨-unitˡ : (l : List Carrier) → [] ∨ l ≡ l
∨-unitˡ [] = PE.refl
∨-unitˡ (x ∷ l) = PE.refl

⊥'-min :  Minimum _≤_ ⊥'
⊥'-min x = []

∨'-unitʳ : (s : Carrier-FP) → (s ∨' ⊥' ≈ s)
∨'-unitʳ (l , f) rewrite ∨-unitʳ l = PW.refl refl~

∨'-unitˡ : (s : Carrier-FP) → (⊥' ∨' s ≈ s) 
∨'-unitˡ (l , f) = PW.refl refl~

x∈l1≤l2 : {x : Carrier} → {l1 l2 : List Carrier} → (f1 : IsFreeList l1) → (f2 : IsFreeList l2) → 
           (x ∈ l1) → (l1 , f1) ≤ (l2 , f2) → (Any (x ⊑_) l2)

x∈l1≤l2 {x} {l1} {l2} f1 f2 x∈l1 l1≤l2 = anyEliminate l1 elim x∈l1
  where
    elim : AnyEliminator {ℓQ = l0} Carrier (Any (x ⊑_) l2) (x ~_) l1
    elim a f x~a a∈≡l1 = LAny.map (λ a⊑· → trans⊑ (reflexive x~a) a⊑·) (LA.lookup l1≤l2 a∈≡l1)

∨'-monoˡ : {a b : Carrier-FP} → (c : Carrier-FP) → a ≤ b → a ∨' c ≤ b ∨' c
∨'-monoˡ {a , fa} {b , fb} (c , fc) a≤b =
  LA.tabulate x∈a∨c→x⊑b∨c
  where
    x∈a∨c→x⊑b∨c : {x : Carrier} → (x ∈≡ a ∨ c) → Any (x ⊑_) (b ∨ c)
    x∈a∨c→x⊑b∨c {x} x∈a∨c with to ⟨$⟩ (a∈≡l→a∈l x∈a∨c) 
      where
        open Equivalence (x∈∨⇔P∨ fa fc (∨-free fa fc) (PW.refl refl~) x)
    x∈a∨c→x⊑b∨c {x} x∈a∨c | inj₁ (x∈a , ¬x⊑c) = from ⟨$⟩ inj₁ (x∈l1≤l2 fa fb x∈a a≤b)
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
∨'-monoʳ {a , fa} {b , fb} (c , fc) a≤b =
  LA.tabulate x∈c∨a→x⊑c∨b
  where
    x∈c∨a→x⊑c∨b : {x : Carrier} → (x ∈≡ c ∨ a) → Any (x ⊑_) (c ∨ b)
    x∈c∨a→x⊑c∨b {x} x∈c∨a with to ⟨$⟩ (a∈≡l→a∈l x∈c∨a) 
      where
        open Equivalence (x∈∨⇔P∨ fc fa (∨-free fc fa) (PW.refl refl~) x)
    x∈c∨a→x⊑c∨b {x} x∈c∨a | inj₁ (x∈c , ¬x⊑a) = 
      from ⟨$⟩ inj₁ (LAny.map (λ x≡· → reflexive x≡·) x∈c)
      where
        open Equivalence (a⊑b∨c⇔a⊑b⊎a⊑c x fc fb)
    x∈c∨a→x⊑c∨b {x} x∈c∨a | inj₂ (inj₁ (x∈a , ¬x⊑c)) =
      from ⟨$⟩ inj₂ (x∈l1≤l2 fa fb x∈a a≤b)
      where
        open Equivalence (a⊑b∨c⇔a⊑b⊎a⊑c x fc fb)
    x∈c∨a→x⊑c∨b {x} x∈c∨a | inj₂ (inj₂ (x∈c , x∈a)) =
      from ⟨$⟩ inj₁ (LAny.map (λ x≡· → reflexive x≡·) x∈c)
      where
        open Equivalence (a⊑b∨c⇔a⊑b⊎a⊑c x fc fb)

∨'-sup : Supremum _≤_ _∨'_ 
∨'-sup (x , fx) (y , fy) = (x≤x∨y , (y≤x∨y , x≤z∧y≤z→x∨y≤z))
  where
    open import Relation.Binary.PartialOrderReasoning FP-Poset

    x≤x∨y : (x , fx) ≤ (x , fx) ∨' (y , fy)
    x≤x∨y = 
      begin
        (x , fx) ≈⟨ PW.symmetric sym~ $ ∨'-unitʳ (x , fx) ⟩
        (x ∨ [] , ∨-free fx []-Free) ≤⟨ ∨'-monoʳ {[] , []-Free} {y , fy} (x , fx) (⊥'-min $ y , fy) ⟩
        (x ∨ y , ∨-free fx fy)
       ∎

    y≤x∨y : (y , fy) ≤ (x , fx) ∨' (y , fy)
    y≤x∨y = 
      begin
        (y , fy) ≈⟨ PW.symmetric sym~ $ ∨'-unitˡ (y , fy) ⟩
        ([] ∨ y , ∨-free []-Free fy) ≤⟨ ∨'-monoˡ {[] , []-Free} {x , fx} (y , fy) (⊥'-min $ x , fx) ⟩
        (x ∨ y , ∨-free fx fy)
       ∎    

    x≤z∧y≤z→x∨y≤z : (z : Carrier-FP) → (x , fx) ≤ z → (y , fy) ≤ z → (x , fx) ∨' (y , fy) ≤ z
    x≤z∧y≤z→x∨y≤z (z , fz) x≤z y≤z = LA.tabulate q∈x∨y→q⊑z 
      where
        q∈x∨y→q⊑z : {q : Carrier} → (q ∈≡ x ∨ y) → Any (q ⊑_) z
        q∈x∨y→q⊑z {q} q∈≡x∨y with to ⟨$⟩ a∈≡l→a∈l q∈≡x∨y
          where
            open Equivalence (x∈∨⇔P∨ fx fy (∨-free fx fy) (PW.refl refl~) q)
        q∈x∨y→q⊑z {q} q∈≡x∨y | inj₁ (q∈x , ¬q⊑y) = 
          x∈l1≤l2 fx fz q∈x x≤z
        q∈x∨y→q⊑z {q} q∈≡x∨y | inj₂ (inj₁ (q∈y , ¬q⊑x)) =
          x∈l1≤l2 fy fz q∈y y≤z
        q∈x∨y→q⊑z {q} q∈≡x∨y | inj₂ (inj₂ (q∈x , q∈y)) =
          x∈l1≤l2 fx fz q∈x x≤z
        

isJoinSemilattice-≤-∨' : IsJoinSemilattice _≈_ _≤_ _∨'_
isJoinSemilattice-≤-∨' = record
  { isPartialOrder = Poset.isPartialOrder FP-Poset
  ; supremum = ∨'-sup
  }

isBoundedJoinSemilattice-≤-∨' : IsBoundedJoinSemilattice _≈_ _≤_ _∨'_ ⊥'
isBoundedJoinSemilattice-≤-∨' = record
  { isJoinSemilattice = isJoinSemilattice-≤-∨'
  ; minimum = ⊥'-min 
  }

-- the "free semilattice" functor F produces a bounded join semilattice when applied to a delta poset
FP-BJS : BoundedJoinSemilattice _ _ _
FP-BJS = record
  { Carrier = Carrier-FP
  ; _≈_ = _≈_
  ; _≤_ = _≤_
  ; _∨_ = _∨'_
  ; ⊥ = ⊥'
  ; isBoundedJoinSemilattice = isBoundedJoinSemilattice-≤-∨'
  }

