
open import SemilatKinding.Core
open import Relation.Binary
open import RelationalStructures
open import Level 
open import Syntax
open import Kinding
open import Util

module SemilatKinding.Product 
  {τL τ₀L τR τ₀R : τ}
  {isSemilatL : IsSemilat τL τ₀L}
  {isSemilatR : IsSemilat τR τ₀R}
  (semSemilatL : SemSemilatIso l0 l0 l0 l0 l0 l0 l0 isSemilatL) 
  (semSemilatR : SemSemilatIso l0 l0 l0 l0 l0 l0 l0 isSemilatR)
 where

open import FreeForgetfulAdjunction
open import SemDeltaPoset 

open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent as PW
open import Data.Sum.Relation.Core
open import Data.List.All
open import Data.Sum
open import Data.List
open import Data.List.Any as LAny
open import Data.List.All as LA
open import Data.List.Relation.Pointwise as LPW hiding (Rel ; Pointwise)
open import Data.Empty
open import Data.Unit renaming (preorder to unitPreorder ; decTotalOrder to unitToset) hiding (_≤_)
open import Data.Bool
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
open import Data.List.Properties as LP

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Relation.Binary.Lattice
open import Function.Inverse
open import Function using (_$_ ; _|>′_ ; const)
open import Function.Equivalence  
open import Function.Equality using (_⟨$⟩_) 
open import SemKinding

semilatCore = ⟦ ProductSemilat isSemilatL isSemilatR ⁂⟧ 

P : DeltaPoset {l0} {l0} {l0} {l0}
P = SemSemilatCore.P semilatCore

deltaL = SemSemilatCore.P ⟦ isSemilatL ⁂⟧
deltaR = SemSemilatCore.P ⟦ isSemilatR ⁂⟧

bjsL = SemSemilatCore.S ⟦ isSemilatL ⁂⟧
bjsR = SemSemilatCore.S ⟦ isSemilatR ⁂⟧

|L| = BoundedJoinSemilattice.Carrier bjsL
|R| = BoundedJoinSemilattice.Carrier bjsR

_≈L_ = BoundedJoinSemilattice._≈_ bjsL
≈L-refl = BoundedJoinSemilattice.Eq.refl bjsL
≈L-reflexive = BoundedJoinSemilattice.Eq.reflexive bjsL
≈L-sym = BoundedJoinSemilattice.Eq.sym bjsL
≈L-trans = BoundedJoinSemilattice.Eq.trans bjsL
≈L-setoid : Setoid _ _
≈L-setoid = record
  { Carrier = |L|
  ; isEquivalence = BoundedJoinSemilattice.isEquivalence bjsL
  }
_≈R_ = BoundedJoinSemilattice._≈_ bjsR
≈R-refl = BoundedJoinSemilattice.Eq.refl bjsR
≈R-reflexive = BoundedJoinSemilattice.Eq.reflexive bjsR
≈R-sym = BoundedJoinSemilattice.Eq.sym bjsR
≈R-trans = BoundedJoinSemilattice.Eq.trans bjsR
≈R-setoid : Setoid _ _
≈R-setoid = record
  { Carrier = |R|
  ; isEquivalence = BoundedJoinSemilattice.isEquivalence bjsR
  }
_≤L_ = BoundedJoinSemilattice._≤_ bjsL
_≤R_ = BoundedJoinSemilattice._≤_ bjsR

_∨L_ = BoundedJoinSemilattice._∨_ bjsL
_∨R_ = BoundedJoinSemilattice._∨_ bjsR

⊥L = BoundedJoinSemilattice.⊥ bjsL
⊥R = BoundedJoinSemilattice.⊥ bjsR

Carrier' : Set
Carrier' = |L| × |R| 

infixr 4 _∨'_
infix 5 _≤'_
infix 6 _≈'_

_≈'_ : Rel Carrier' _
_≈'_ = Pointwise _≈L_ _≈R_

_≤'_ : Rel Carrier' _
_≤'_ = Pointwise _≤L_ _≤R_

_∨'_ : Carrier' → Carrier' → Carrier'
(aL , aR) ∨' (bL , bR) = (aL ∨L bL) , (aR ∨R bR) 

⊥' : Carrier'
⊥' = (⊥L , ⊥R)

|L₀| = DeltaPoset.Carrier deltaL
|R₀| = DeltaPoset.Carrier deltaR

Carrier₀ = |L₀| ⊎ |R₀|  

_≈L₀_ : |L₀| → |L₀| → Set  
_≈L₀_ = DeltaPoset._≈_ deltaL
≈L₀-sym = DeltaPoset.sym≈ deltaL
≈L₀-refl = DeltaPoset.refl≈ deltaL
≈L₀-reflexive = DeltaPoset.reflexive≈ deltaL
≈L₀-trans = DeltaPoset.trans≈ deltaL
≈L₀-setoid : Setoid _ _
≈L₀-setoid = record
  { Carrier = |L₀|
  ; isEquivalence = DeltaPoset.Eq.isEquivalence deltaL
  }
_≈R₀_ : |R₀| → |R₀| → Set
_≈R₀_ = DeltaPoset._≈_ deltaR
≈R₀-sym = DeltaPoset.sym≈ deltaR
≈R₀-refl = DeltaPoset.refl≈ deltaR
≈R₀-reflexive = DeltaPoset.reflexive≈ deltaR
≈R₀-trans = DeltaPoset.trans≈ deltaR
≈R₀-setoid : Setoid _ _
≈R₀-setoid = record
  { Carrier = |R₀|
  ; isEquivalence = DeltaPoset.Eq.isEquivalence deltaR
  }
_⊑L₀_ : |L₀| → |L₀| → Set
_⊑L₀_ = DeltaPoset._⊑_ deltaL
_⊑R₀_ : |R₀| → |R₀| → Set
_⊑R₀_ = DeltaPoset._⊑_ deltaR
_∥L₀_ : |L₀| → |L₀| → Set
_∥L₀_ = DeltaPoset._∥_ deltaL
_∥R₀_ : |R₀| → |R₀| → Set
_∥R₀_ = DeltaPoset._∥_ deltaR
_∦L₀_ : |L₀| → |L₀| → Set
_∦L₀_ = DeltaPoset._∦_ deltaL
_∦L₀?_ = DeltaPoset._∦?_ deltaL
_∦R₀_ : |R₀| → |R₀| → Set
_∦R₀_ = DeltaPoset._∦_ deltaR
_∦R₀?_ = DeltaPoset._∦?_ deltaR
_<L₀_ : |L₀| → |L₀| → Set
_<L₀_ = DeltaPoset._<_ deltaL
<L₀-trans = DeltaPoset.trans< deltaL
irreflL₀ = DeltaPoset.irrefl deltaL
compareL₀ = DeltaPoset.compare deltaL
_<R₀_ : |R₀| → |R₀| → Set
_<R₀_ = DeltaPoset._<_ deltaR
<R₀-trans = DeltaPoset.trans< deltaR
irreflR₀ = DeltaPoset.irrefl deltaR
compareR₀ = DeltaPoset.compare deltaR

|P| : Set
|P| = DeltaPoset.Carrier P

_≈P_ : |P| → |P| → Set
_≈P_ = DeltaPoset._≈_ P

≈P-setoid : Setoid _ _
≈P-setoid = DeltaPoset.≈-setoid P
≈P-reflexive = DeltaPoset.Eq.reflexive P
≈P-refl = DeltaPoset.Eq.refl P
≈P-trans = DeltaPoset.Eq.trans P
≈P-sym = DeltaPoset.Eq.sym P

_<P_ : |P| → |P| → Set
_<P_ = DeltaPoset._<_ P

_⊑P_ : |P| → |P| → Set
_⊑P_ = DeltaPoset._⊑_ P

_∦P_ : |P| → |P| → Set
_∦P_ = DeltaPoset._∦_ P

_∦P?_ = DeltaPoset._∦?_ P
compareP = DeltaPoset.compare P

∦P-sym = DeltaPoset.∦-sym P

_∥P_ : |P| → |P| → Set
_∥P_ = DeltaPoset._∥_ P

open import FreeSemilattice P renaming 
  (⊥ to ⊥F ; _∨_ to _∨F_ ; _≈_ to _≈F_ ; _~_ to _~F_ ; ≈-refl to ≈F-refl ; SemilatCarrier to Carrier-FP ;
   ≈-reflexive to ≈F-reflexive ; FP-BJS to FP-BJS ; ∨-identityˡ to ∨F-identityˡ ; ∨-identityʳ to ∨F-identityʳ ; 
   ⊑-refl to ⊑P-refl ; ⊑-reflexive to ⊑P-reflexive ; ⊑-trans to ⊑P-trans ; ⊑-decPoset to ⊑P-decPoset ;
   ≈-sym to ≈F-sym ; ∨-congˡ to ∨F-congˡ ; ∨-congʳ to ∨F-congʳ ; ∨-assoc to ∨F-assoc ; ∨-comm to ∨F-comm ;
   _∈_ to _∈P_ ; _∈'_ to _∈P'_ ; FP-setoid to FP-setoid ; c1≈c2⇔sameElements to c1≈c2⇔sameElementsP ;
   P∨ to P-P∨ ; x∈∨⇔P∨ to x∈∨⇔P∨-P ; p∈c1≈c2 to p∈c1≈c2-P ; concat-F to concat-F) 
open import FreeSemilattice deltaL renaming 
  (IsFreeList to IsFreeListL ; []-Free to []-FreeL ; ∷-Free to ∷-FreeL ; _≈_ to _≈FL_ ; ⊥ to ⊥FL ; 
   SemilatCarrier to Carrier-FPL ; _∨_ to _∨FL_ ; FP-BJS to FPL-BJS ; FP-setoid to FPL-setoid ;
   ∨-identityˡ to ∨FL-identityˡ ; ∨-identityʳ to ∨FL-identityʳ ; ⊑-refl to ⊑L₀-refl ; ⊑-reflexive to ⊑L₀-reflexive ;
   ⊑-trans to ⊑L₀-trans ; ⊑-respˡ-≈ to ⊑L₀-respˡ-≈L₀ ; ⊑-respʳ-≈ to ⊑L₀-respʳ-≈L₀ ; 
   sng-free to sng-freeL ; _≤_ to _≤FL_ ; ≈-sym to ≈FL-sym ; ≈-trans to ≈FL-trans ; ≈-refl to ≈FL-refl ; 
   ≈-reflexive to ≈FL-reflexive ; 
   _∈_ to _∈L_ ; _∈'_ to _∈L'_ ;
   c1≈c2⇔sameElements to c1≈c2⇔sameElementsL ; p∈c1≈c2 to p∈c1≈c2-L ; x∈∨⇔P∨ to x∈∨⇔P∨-L ;
   concat-F to concat-FR)
open import FreeSemilattice deltaR renaming 
  (IsFreeList to IsFreeListR ; []-Free to []-FreeR ; ∷-Free to ∷-FreeR ; _≈_ to _≈FR_ ; ⊥ to ⊥FR ; 
   SemilatCarrier to Carrier-FPR ; _∨_ to _∨FR_ ; FP-BJS to FPR-BJS ; FP-setoid to FPR-setoid ;
   ∨-identityˡ to ∨FR-identityˡ ; ∨-identityʳ to ∨FR-identityʳ ; ⊑-refl to ⊑R₀-refl ; ⊑-reflexive to ⊑R₀-reflexive ;
   ⊑-trans to ⊑R₀-trans ; ⊑-respˡ-≈ to ⊑R₀-respˡ-≈R₀ ; ⊑-respʳ-≈ to ⊑R₀-respʳ-≈R₀ ;
   sng-free to sng-freeR ; _≤_ to _≤FR_ ; ≈-sym to ≈FR-sym ; ≈-trans to ≈FR-trans ; ≈-refl to ≈FR-refl ; 
   ≈-reflexive to ≈FR-reflexive ; _∈_ to _∈R_ ; _∈'_ to _∈R'_ ;
   c1≈c2⇔sameElements to c1≈c2⇔sameElementsR ; p∈c1≈c2 to p∈c1≈c2-R ; x∈∨⇔P∨ to x∈∨⇔P∨-R ;
   concat-F to concat-FL)

|fL| : |L| → Σ[ l ∈ List (DeltaPoset.Carrier deltaL) ] (IsFreeListL l)
|fL| = proj₁ $ SemSemilatIso.f semSemilatL

|fL|-≈ : ∀ (a b : |L|) → a ≈L b → (|fL| a) ≈FL (|fL| b)
|fL|-≈ = proj₁ $ proj₂ $ SemSemilatIso.f semSemilatL

|fL|-⊥ : |fL| ⊥L ≈FL ⊥FL
|fL|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilatIso.f semSemilatL

|fL|-∨ : ∀ (a b : |L|) → |fL| (a ∨L b) ≈FL ( (|fL| a) ∨FL (|fL| b) ) 
|fL|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilatIso.f semSemilatL

|fR| : |R| → Σ[ l ∈ List (DeltaPoset.Carrier deltaR) ] (IsFreeListR l)
|fR| = proj₁ $ SemSemilatIso.f semSemilatR

|fR|-≈ : ∀ (a b : |R|) → a ≈R b → (|fR| a) ≈FR (|fR| b)
|fR|-≈ = proj₁ $ proj₂ $ SemSemilatIso.f semSemilatR

|fR|-⊥ : |fR| ⊥R ≈FR ⊥FR
|fR|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilatIso.f semSemilatR

|fR|-∨ : ∀ (a b : |R|) → |fR| (a ∨R b) ≈FR ( (|fR| a) ∨FR (|fR| b) ) 
|fR|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilatIso.f semSemilatR

gL = SemSemilatIso.g semSemilatL

|gL| : Carrier-FPL → |L|
|gL| = proj₁ $ SemSemilatIso.g semSemilatL

|gL|-≈ : (a b : Carrier-FPL) → a ≈FL b → (|gL| a) ≈L (|gL| b) 
|gL|-≈ = proj₁ $ proj₂ $ SemSemilatIso.g semSemilatL

|gL|-⊥ : (|gL| ⊥FL) ≈L ⊥L
|gL|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilatIso.g semSemilatL

|gL|-∨ : ∀ (a b : Carrier-FPL) → |gL| (a ∨FL b) ≈L ( (|gL| a) ∨L (|gL| b) ) 
|gL|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilatIso.g semSemilatL

L-inv-S→FP→S = SemSemilatIso.inv-S→FP→S semSemilatL
L-inv-FP→S→FP = SemSemilatIso.inv-FP→S→FP semSemilatL

gR = SemSemilatIso.g semSemilatR

|gR| : Carrier-FPR → |R|
|gR| = proj₁ $ SemSemilatIso.g semSemilatR

|gR|-≈ : (a b : Carrier-FPR) → a ≈FR b → (|gR| a) ≈R (|gR| b) 
|gR|-≈ = proj₁ $ proj₂ $ SemSemilatIso.g semSemilatR

|gR|-⊥ : (|gR| ⊥FR) ≈R ⊥R
|gR|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilatIso.g semSemilatR

|gR|-∨ : ∀ (a b : Carrier-FPR) → |gR| (a ∨FR b) ≈R ( (|gR| a) ∨R (|gR| b) ) 
|gR|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilatIso.g semSemilatR

R-inv-S→FP→S = SemSemilatIso.inv-S→FP→S semSemilatR
R-inv-FP→S→FP = SemSemilatIso.inv-FP→S→FP semSemilatR

convL : (z : List |L₀|) → (f : IsFreeListL z) → 
        Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) z (proj₁ l))
--[[[
convL [] []-FreeL = ([] , []-Free) , []
convL (h ∷ t) (∷-FreeL h t min incomp ft) = 
  ((inj₁ h) ∷ t' , ∷-Free (inj₁ h) t' min' incomp' ft') , (PE.refl ∷ eqt')
  where
    imp1 : ∀ {a : |L₀|} → {b : |P|} → (h <L₀ a) → (b ≡ inj₁ a) → (inj₁ h <P b)
    imp1 {a} {b} h<a b≡injA@PE.refl = ₁∼₁ h<a  

    r : Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) t (proj₁ l))
    r = convL t ft

    t' : List |P|
    t' = proj₁ $ proj₁ r

    ft' : IsFreeList t'
    ft' = proj₂ $ proj₁ r

    eqt' : LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) t t'
    eqt' = proj₂ r

    min' : All (λ z → inj₁ h <P z) t'
    min' = pointwiseRespAll imp1 t t' min eqt'

    ⊑-resp-inj₁ : {a b : |L₀|} → inj₁ a ⊑P inj₁ b → a ⊑L₀ b
    ⊑-resp-inj₁ {a} {b} (₁∼₁ a⊑b) = a⊑b

    p : {a : |P|} → {b : |L₀|} → a ∈≡ t' → (a ≡ inj₁ b) → b ∈≡ t
    p {a} {b} a∈≡t' a≡injb = pointwiseRespAny imp t' t a∈≡t' (LPW.symmetric PE.sym eqt')  
      where
        open import Data.Sum.Properties
        imp : ∀ {x : |P|} → {y : |L₀|} → (a ≡ x) → (inj₁ y ≡ x) → (b ≡ y) 
        imp {x} {y} PE.refl PE.refl = inj₁-injective (PE.sym a≡injb) 

    incomp' : ¬ Any (λ z → inj₁ h ∦P z) t'
    incomp' injh∦t' = anyEliminate t' eliminator injh∦t'
      where
        eliminator : AnyEliminator {ℓQ = l0} |P| ⊥ (inj₁ h ∦P_) t'
        eliminator (inj₁ a') f (inj₂ injh⊑inja') inja'∈≡t' = incomp $ LAny.map (λ a'≡· → PE.subst (h ∦L₀_) a'≡· h∦a') (p inja'∈≡t' PE.refl)    
          where
            h∦a' : h ∦L₀ a'
            h∦a' = inj₂ (⊑-resp-inj₁ injh⊑inja')
        eliminator (inj₁ a') f (inj₁ inja'⊑injh) inja'∈≡t' = incomp $ LAny.map (λ a'≡· → PE.subst (h ∦L₀_) a'≡· h∦a') (p inja'∈≡t' PE.refl)    
          where
            h∦a' : h ∦L₀ a'
            h∦a' = inj₁ (⊑-resp-inj₁ inja'⊑injh)

        eliminator (inj₂ a') f (inj₁ (₁∼₂ ())) inja'∈≡t'
        eliminator (inj₂ a') f (inj₂ ()) inja'∈≡t'
--]]]

convR : (z : List |R₀|) → IsFreeListR z → 
        Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₂ x)) z (proj₁ l))
--[[[
convR [] []-FreeR = ([] , []-Free) , []
convR (h ∷ t) (∷-FreeR h t min incomp ft) =  
  ((inj₂ h) ∷ t' , ∷-Free (inj₂ h) t' min' incomp' ft') , (PE.refl ∷ eqt')
  where
    imp1 : ∀ {a : |R₀|} → {b : |P|} → (h <R₀ a) → (b ≡ inj₂ a) → (inj₂ h <P b)
    imp1 {a} {b} h<a b≡injA@PE.refl = ₂∼₂ h<a  

    r : Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₂ x)) t (proj₁ l))
    r = convR t ft

    t' : List |P|
    t' = proj₁ $ proj₁ r

    ft' : IsFreeList t'
    ft' = proj₂ $ proj₁ r

    eqt' : LPW.Pointwise (λ x → λ y → (y ≡ inj₂ x)) t t'
    eqt' = proj₂ r

    min' : All (λ z → inj₂ h <P z) t'
    min' = pointwiseRespAll imp1 t t' min eqt'

    ⊑-resp-inj₂ : {a b : |R₀|} → inj₂ a ⊑P inj₂ b → a ⊑R₀ b
    ⊑-resp-inj₂ {a} {b} (₂∼₂ a⊑b) = a⊑b

    p : {a : |P|} → {b : |R₀|} → a ∈≡ t' → (a ≡ inj₂ b) → b ∈≡ t
    p {a} {b} a∈≡t' a≡injb = pointwiseRespAny imp t' t a∈≡t' (LPW.symmetric PE.sym eqt')  
      where
        open import Data.Sum.Properties
        imp : ∀ {x : |P|} → {y : |R₀|} → (a ≡ x) → (inj₂ y ≡ x) → (b ≡ y) 
        imp {x} {y} PE.refl PE.refl = inj₂-injective (PE.sym a≡injb) 

    incomp' : ¬ Any (λ z → inj₂ h ∦P z) t'
    incomp' injh∦t' = anyEliminate t' eliminator injh∦t'
      where
        eliminator : AnyEliminator {ℓQ = l0} |P| ⊥ (inj₂ h ∦P_) t'
        eliminator (inj₂ a') f (inj₂ injh⊑inja') inja'∈≡t' = incomp $ LAny.map (λ a'≡· → PE.subst (h ∦R₀_) a'≡· h∦a') (p inja'∈≡t' PE.refl)    
          where
            h∦a' : h ∦R₀ a'
            h∦a' = inj₂ (⊑-resp-inj₂ injh⊑inja')
        eliminator (inj₂ a') f (inj₁ inja'⊑injh) inja'∈≡t' = incomp $ LAny.map (λ a'≡· → PE.subst (h ∦R₀_) a'≡· h∦a') (p inja'∈≡t' PE.refl)    
          where
            h∦a' : h ∦R₀ a'
            h∦a' = inj₁ (⊑-resp-inj₂ inja'⊑injh)

        eliminator (inj₁ a') f (inj₁ ()) inja'∈≡t'
        eliminator (inj₁ a') f (inj₂ (₁∼₂ ())) inja'∈≡t'
--]]]

convL' : Carrier-FPL → Carrier-FP
convL' (x , f) = proj₁ (convL x f)

convR' : Carrier-FPR → Carrier-FP
convR' (x , f) = proj₁ (convR x f)

convL'-resp-≈FL : {c1 c2 : Carrier-FPL} → (c1 ≈FL c2) → (convL' c1) ≈F (convL' c2) 
--[[[
convL'-resp-≈FL {.[] , []-FreeL} {.[] , []-FreeL} [] = ≈F-reflexive {convL' $ [] , []-FreeL} PE.refl
convL'-resp-≈FL {h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1} {h2 ∷ t2 , ∷-FreeL _ _ min2 incomp2 ft2} (h1~h2 ∷ t1≈t2) = 
  let
    conv-t1≈t2 : (convL' $ t1 , ft1) ≈F (convL' $ t2 , ft2)
    conv-t1≈t2 = convL'-resp-≈FL t1≈t2

    conv-h1-h2 : (inj₁ h1) ~F (inj₁ h2)
    conv-h1-h2 = ₁∼₁ h1~h2
  in
  conv-h1-h2 ∷ conv-t1≈t2
--]]]

convR'-resp-≈FR : {c1 c2 : Carrier-FPR} → (c1 ≈FR c2) → (convR' c1) ≈F (convR' c2) 
--[[[
convR'-resp-≈FR {.[] , []-FreeL} {.[] , []-FreeL} [] = ≈F-reflexive {convL' $ [] , []-FreeL} PE.refl
convR'-resp-≈FR {h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1} {h2 ∷ t2 , ∷-FreeL _ _ min2 incomp2 ft2} (h1~h2 ∷ t1≈t2) = 
  let
    conv-t1≈t2 : (convR' $ t1 , ft1) ≈F (convR' $ t2 , ft2)
    conv-t1≈t2 = convR'-resp-≈FR t1≈t2

    conv-h1-h2 : (inj₂ h1) ~F (inj₂ h2)
    conv-h1-h2 = ₂∼₂ h1~h2
  in
  conv-h1-h2 ∷ conv-t1≈t2
--]]]

open DeltaPoset.Comparison

convL'-preserves-∨ : (c1 c2 : Carrier-FPL) → ( (convL' (c1 ∨FL c2)) ≈F ( (convL' c1) ∨F (convL' c2) ) )
--[[[
convL'-preserves-∨ ([] , []-FreeL) ([] , []-FreeL) = []
convL'-preserves-∨ ([] , []-FreeL) c2@(h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) = 
  begin 
     convL' (([] , []-FreeL) ∨FL c2) ≈⟨ p ⟩
     convL' c2 ≈⟨ q ⟩ 
     (convL' $ [] , []-FreeL) ∨F (convL' c2)  
   ∎
  where
    open import Relation.Binary.EqReasoning FP-setoid
    p : (convL' (([] , []-FreeL) ∨FL c2)) ≈F (convL' c2)
    p = convL'-resp-≈FL {([] , []-FreeL) ∨FL c2} {c2} $ ∨FL-identityˡ c2

    q : (convL' c2) ≈F ((convL' $ [] , []-FreeL) ∨F (convL' c2))
    q = ≈F-sym {i = convL' c2} {j = (convL' ([] , []-FreeL)) ∨F (convL' c2)} $ ∨F-identityˡ (convL' c2)
convL'-preserves-∨ c1@(h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) ([] , []-FreeL) = 
   begin 
     convL' (c1 ∨FL ([] , []-FreeL)) ≈⟨ p ⟩
     convL' c1 ≈⟨ q ⟩ 
     (convL' c1) ∨F (convL' $ [] , []-FreeL)   
   ∎
  where
    open import Relation.Binary.EqReasoning FP-setoid
    p : (convL' (c1 ∨FL ([] , []-FreeL))) ≈F (convL' c1)
    p = convL'-resp-≈FL {c1 ∨FL ([] , []-FreeL)} {c1} $ ∨FL-identityʳ c1

    q : (convL' c1) ≈F ((convL' c1) ∨F (convL' $ [] , []-FreeL))
    q = ≈F-sym {i = convL' c1} {j = (convL' ([] , []-FreeL)) ∨F (convL' c1)} $ ∨F-identityʳ (convL' c1)
convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , ∷-FreeL _ _ min2 incomp2 ft2) with h1 ∦L₀? h2 | (inj₁ h1) ∦P? (inj₁ h2) 
convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
  convL'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | r⊑l ¬ih1⊑ih2 (₁∼₁ h2⊑h1) =
  ⊥-elim $ ¬h2⊑h1 h2⊑h1
convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l≈r ih1~ih2 =
  convL'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r ih1∥ih2 =
  ⊥-elim $ ih1∥ih2 (inj₁ $ ₁∼₁ h1⊑h2)
convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
  ⊥-elim $ ¬ih2⊑ih1 (₁∼₁ h2⊑h1)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | r⊑l ¬ih1⊑ih2 (₁∼₁ _) =
  convL'-preserves-∨ (h1 ∷ t1 , f1) (t2 , ft2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l≈r (₁∼₁ h1~h2) =
  ⊥-elim $ ¬h1⊑h2 (⊑L₀-reflexive h1~h2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l∥r ih1∥ih2 =
  ⊥-elim $ ih1∥ih2 (inj₂ $ ₁∼₁ h2⊑h1)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
  ⊥-elim $ ¬ih2⊑ih1 (₁∼₁ $ ⊑L₀-reflexive (≈L₀-sym h1~h2))
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l≈r h1~h2 | r⊑l ¬ih1⊑ih2 (₁∼₁ _) =
  ⊥-elim $ ¬ih1⊑ih2 (₁∼₁ $ ⊑L₀-reflexive h1~h2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l≈r (₁∼₁ _) =
  convL'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l∥r ih1∥ih2 =
  ⊥-elim $ ih1∥ih2 (inj₁ (₁∼₁ $ ⊑L₀-reflexive h1~h2))
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l⊑r (₁∼₁ h1⊑h2) ¬ih2⊑ih1 =
  ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | r⊑l ¬ih1⊑ih2 (₁∼₁ h2⊑h1) =
  ⊥-elim $ h1∥h2 (inj₂ h2⊑h1)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l≈r (₁∼₁ h1≈h2) =
  ⊥-elim $ h1∥h2 (inj₁ $ ⊑L₀-reflexive h1≈h2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 with compareL₀ h1 h2 | compareP (inj₁ h1) (inj₁ h2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri< (₁∼₁ _) _ _ =
  (₁∼₁ $ ≈L₀-refl) ∷ convL'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri≈ _ (₁∼₁ h1~h2) _ =
  ⊥-elim $ irreflL₀ h1~h2 h1<h2
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri> _ _ (₁∼₁ h2<h1) =
  ⊥-elim $ irreflL₀ ≈L₀-refl (<L₀-trans h1<h2 h2<h1)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri< (₁∼₁ h1<h2) _ _ =
  ⊥-elim $ h1∥h2 (inj₁ $ ⊑L₀-reflexive h1~h2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri≈ _ (₁∼₁ _) _ =
  ⊥-elim $ h1∥h2 (inj₁ $ ⊑L₀-reflexive h1~h2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri> _ _ (₁∼₁ h2<h1) =
  ⊥-elim $ h1∥h2 (inj₁ $ ⊑L₀-reflexive h1~h2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri< (₁∼₁ h1<h2) _ _ =
  ⊥-elim $ irreflL₀ ≈L₀-refl (<L₀-trans h1<h2 h2<h1)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri≈ _ (₁∼₁ h1~h2) _ =
  ⊥-elim $ h1∥h2 (inj₁ $ ⊑L₀-reflexive h1~h2)
convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri> _ _ (₁∼₁ _) =
  (₁∼₁ $ ≈L₀-refl) ∷ convL'-preserves-∨ (h1 ∷ t1 , f1) (t2 , ft2)
--]]]

convR'-preserves-∨ : (c1 c2 : Carrier-FPR) → ( (convR' (c1 ∨FR c2)) ≈F ( (convR' c1) ∨F (convR' c2) ) )  
--[[[
convR'-preserves-∨ ([] , []-FreeR) ([] , []-FreeR) = []
convR'-preserves-∨ ([] , []-FreeR) c2@(h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) = 
  begin 
     convR' (([] , []-FreeR) ∨FR c2) ≈⟨ p ⟩
     convR' c2 ≈⟨ q ⟩ 
     (convR' $ [] , []-FreeR) ∨F (convR' c2)  
   ∎
  where
    open import Relation.Binary.EqReasoning FP-setoid
    p : (convR' (([] , []-FreeR) ∨FR c2)) ≈F (convR' c2)
    p = convR'-resp-≈FR {([] , []-FreeR) ∨FR c2} {c2} $ ∨FR-identityˡ c2

    q : (convR' c2) ≈F ((convR' $ [] , []-FreeR) ∨F (convR' c2))
    q = ≈F-sym {i = convR' c2} {j = (convR' ([] , []-FreeR)) ∨F (convR' c2)} $ ∨F-identityˡ (convR' c2)
convR'-preserves-∨ c1@(h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) ([] , []-FreeR) = 
   begin 
     convR' (c1 ∨FR ([] , []-FreeR)) ≈⟨ p ⟩
     convR' c1 ≈⟨ q ⟩ 
     (convR' c1) ∨F (convR' $ [] , []-FreeR)   
   ∎
  where
    open import Relation.Binary.EqReasoning FP-setoid
    p : (convR' (c1 ∨FR ([] , []-FreeR))) ≈F (convR' c1)
    p = convR'-resp-≈FR {c1 ∨FR ([] , []-FreeR)} {c1} $ ∨FR-identityʳ c1

    q : (convR' c1) ≈F ((convR' c1) ∨F (convR' $ [] , []-FreeR))
    q = ≈F-sym {i = convR' c1} {j = (convR' ([] , []-FreeR)) ∨F (convR' c1)} $ ∨F-identityʳ (convR' c1)
convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , ∷-FreeR _ _ min2 incomp2 ft2) with h1 ∦R₀? h2 | (inj₂ h1) ∦P? (inj₂ h2) 
convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
  convR'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | r⊑l ¬ih1⊑ih2 (₂∼₂ h2⊑h1) =
  ⊥-elim $ ¬h2⊑h1 h2⊑h1
convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l≈r ih1~ih2 =
  convR'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r ih1∥ih2 =
  ⊥-elim $ ih1∥ih2 (inj₁ $ ₂∼₂ h1⊑h2)
convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
  ⊥-elim $ ¬ih2⊑ih1 (₂∼₂ h2⊑h1)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | r⊑l ¬ih1⊑ih2 (₂∼₂ _) =
  convR'-preserves-∨ (h1 ∷ t1 , f1) (t2 , ft2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l≈r (₂∼₂ h1~h2) =
  ⊥-elim $ ¬h1⊑h2 (⊑R₀-reflexive h1~h2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l∥r ih1∥ih2 =
  ⊥-elim $ ih1∥ih2 (inj₂ $ ₂∼₂ h2⊑h1)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
  ⊥-elim $ ¬ih2⊑ih1 (₂∼₂ $ ⊑R₀-reflexive (≈R₀-sym h1~h2))
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l≈r h1~h2 | r⊑l ¬ih1⊑ih2 (₂∼₂ _) =
  ⊥-elim $ ¬ih1⊑ih2 (₂∼₂ $ ⊑R₀-reflexive h1~h2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l≈r (₂∼₂ _) =
  convR'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l∥r ih1∥ih2 =
  ⊥-elim $ ih1∥ih2 (inj₁ (₂∼₂ $ ⊑R₀-reflexive h1~h2))
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l⊑r (₂∼₂ h1⊑h2) ¬ih2⊑ih1 =
  ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | r⊑l ¬ih1⊑ih2 (₂∼₂ h2⊑h1) =
  ⊥-elim $ h1∥h2 (inj₂ h2⊑h1)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l≈r (₂∼₂ h1≈h2) =
  ⊥-elim $ h1∥h2 (inj₁ $ ⊑R₀-reflexive h1≈h2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 with compareR₀ h1 h2 | compareP (inj₂ h1) (inj₂ h2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri< (₂∼₂ _) _ _ =
  (₂∼₂ $ ≈R₀-refl) ∷ convR'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri≈ _ (₂∼₂ h1~h2) _ =
  ⊥-elim $ irreflR₀ h1~h2 h1<h2
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri> _ _ (₂∼₂ h2<h1) =
  ⊥-elim $ irreflR₀ ≈R₀-refl (<R₀-trans h1<h2 h2<h1)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri< (₂∼₂ h1<h2) _ _ =
  ⊥-elim $ h1∥h2 (inj₁ $ ⊑R₀-reflexive h1~h2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri≈ _ (₂∼₂ _) _ =
  ⊥-elim $ h1∥h2 (inj₁ $ ⊑R₀-reflexive h1~h2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri> _ _ (₂∼₂ h2<h1) =
  ⊥-elim $ h1∥h2 (inj₁ $ ⊑R₀-reflexive h1~h2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri< (₂∼₂ h1<h2) _ _ =
  ⊥-elim $ irreflR₀ ≈R₀-refl (<R₀-trans h1<h2 h2<h1)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri≈ _ (₂∼₂ h1~h2) _ =
  ⊥-elim $ h1∥h2 (inj₁ $ ⊑R₀-reflexive h1~h2)
convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri> _ _ (₂∼₂ _) =
  (₂∼₂ $ ≈R₀-refl) ∷ convR'-preserves-∨ (h1 ∷ t1 , f1) (t2 , ft2)
--]]]

pL : proj₁ (|fL| ⊥L) ≡ []
pL = pointwise-[]ʳ |fL|-⊥ 

pL' : (|fL| ⊥L) ≡ ([] , []-FreeL)
pL' with |fL| ⊥L | pL
pL' | ([] , []-FreeR) | PE.refl  = PE.refl
pL' | (h ∷ t , ∷-FreeR _ _ _ _ _) | ()

pR : proj₁ (|fR| ⊥R) ≡ []
pR = pointwise-[]ʳ |fR|-⊥ 

pR' : (|fR| ⊥R) ≡ ([] , []-FreeR)
pR' with |fR| ⊥R | pR
pR' | ([] , []-FreeR) | PE.refl  = PE.refl
pR' | (h ∷ t , ∷-FreeR _ _ _ _ _) | ()

convL-⊥ : proj₁ (convL (proj₁ $ |fL| ⊥L) (proj₂ $ |fL| ⊥L)) ≡ ⊥F
convL-⊥ rewrite pL' = PE.refl

convR-⊥ : proj₁ (convR (proj₁ $ |fR| ⊥R) (proj₂ $ |fR| ⊥R)) ≡ ⊥F
convR-⊥ rewrite pR' = PE.refl

P-|f| : (a : Carrier') → (x : |P|) → Set
P-|f| (aL , aR) x = (Σ[ y ∈ |L₀| ] (x ≈P inj₁ y) × (y ∈L |fL| aL)) ⊎ (Σ[ y ∈ |R₀| ] (x ≈P inj₂ y) × (y ∈R |fR| aR))

|f|-aux : (a : Carrier') → Σ[ c ∈ Carrier-FP ] ∀ (x : |P|) → x ∈P c ⇔ P-|f| a x 
--[[[

|f|-aux (aL , aR) =
  let
    res , _ = concat-F (resL-list , resL-free) (resR-list , resR-free) min incomp
  in
    res , res-prop⇔
  where
    --open import FreeSemilattice.Core P using (concat-F)

    factoredL : Σ[ l ∈ List |L₀| ] (IsFreeListL l)
    factoredL = |fL| aL

    factoredR : Σ[ l ∈ List |R₀| ] (IsFreeListR l)
    factoredR = |fR| aR

    resL : Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) (proj₁ factoredL) (proj₁ l))
    resL = convL (proj₁ factoredL) (proj₂ factoredL)

    resR : Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₂ x)) (proj₁ factoredR) (proj₁ l))
    resR = convR (proj₁ factoredR) (proj₂ factoredR)

    resL-list : List |P|
    resL-list = proj₁ $ proj₁ resL

    resR-list : List |P|
    resR-list = proj₁ $ proj₁ resR

    resL-free : IsFreeList resL-list
    resL-free = proj₂ $ proj₁ resL

    resR-free : IsFreeList resR-list
    resR-free = proj₂ $ proj₁ resR

    resL-eq : (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) (proj₁ factoredL) resL-list)
    resL-eq = proj₂ resL

    resR-eq : (LPW.Pointwise (λ x → λ y → (y ≡ inj₂ x)) (proj₁ factoredR) resR-list)
    resR-eq = proj₂ resR

    min : All (λ x → All (x <P_) resR-list) resL-list
    min = pointwiseRespAll imp (proj₁ factoredL) resL-list U-L resL-eq
      where
        open import Relation.Unary using (Universal ; U)
        open import Relation.Unary.Properties
        open import Data.List.All.Properties

        U-L : All U (proj₁ factoredL)
        U-L = All-universal U-Universal (proj₁ factoredL)

        U-R : All U (proj₁ factoredR)
        U-R = All-universal U-Universal (proj₁ factoredR)

        imp : ∀ {a b} → U a → (b ≡ inj₁ a) → All (b <P_) resR-list
        imp {a} {b} _ b≡inj₁a = pointwiseRespAll imp' (proj₁ factoredR) resR-list U-R resR-eq
          where 
            imp' : ∀ {x y} → U x → (y ≡ inj₂ x) → b <P y
            imp' {x} {y} _ y≡inj₂x rewrite b≡inj₁a | y≡inj₂x = ₁∼₂ tt 

    incomp : All (λ x → All (x ∥P_) resR-list) resL-list
    incomp = pointwiseRespAll imp (proj₁ factoredL) resL-list U-L resL-eq
      where
        open import Relation.Unary using (Universal ; U)
        open import Relation.Unary.Properties
        open import Data.List.All.Properties

        U-L : All U (proj₁ factoredL)
        U-L = All-universal U-Universal (proj₁ factoredL)

        U-R : All U (proj₁ factoredR)
        U-R = All-universal U-Universal (proj₁ factoredR)        

        imp : ∀ {a b} → U a → (b ≡ inj₁ a) → All (b ∥P_) resR-list
        imp {a} {b} _ PE.refl = pointwiseRespAll imp' (proj₁ factoredR) resR-list U-R resR-eq
          where 
            imp' : ∀ {x y} → U x → (y ≡ inj₂ x) → b ∥P y
            imp' {x} {.(inj₂ x)} _ PE.refl (inj₁ (₁∼₂ ()))
            imp' {x} {.(inj₂ x)} _ PE.refl (inj₂ ()) 

    res : Carrier-FP
    res = proj₁ $ concat-F (resL-list , resL-free) (resR-list , resR-free) min incomp

    concat-property : (proj₁ res) ≡ (resL-list) ++ (resR-list)
    concat-property = proj₂ $ concat-F (resL-list , resL-free) (resR-list , resR-free) min incomp

    res-prop← : ∀ (x : |P|) → (Σ[ y ∈ |L₀| ] (x ≈P inj₁ y) × (y ∈L |fL| aL)) ⊎ (Σ[ y ∈ |R₀| ] (x ≈P inj₂ y) × (y ∈R |fR| aR)) → 
                    (x ∈P res)
    res-prop← x (inj₁ (y , x-≈P-inj₁y , y-∈L~fLaL)) rewrite concat-property = ∈-++⁺ˡ ≈P-setoid p''
      where
        open import Data.List.Membership.Setoid.Properties
        imp : ∀ {a : |P|} → {b : |L₀|} → (y ≈L₀ b) → (a ≡ inj₁ b) → (a ≈P inj₁ y)
        imp {a} {b} y-≈L₀-b a-≡-inj₁b = DeltaPoset.Eq.trans P a-≈P-inj₁b (₁∼₁ (≈L₀-sym y-≈L₀-b))  
          where
            open Setoid ≈P-setoid

            a-≈P-inj₁b : a ≈P inj₁ b
            a-≈P-inj₁b = ≈P-reflexive a-≡-inj₁b

        -- step 1 : since y ∈L fLaL, we have inj₁ y ∈P convL fLaL
        p : Any (λ · → · ≈P inj₁ y) resL-list
        p = pointwiseRespAny imp (proj₁ $ |fL| aL) resL-list y-∈L~fLaL resL-eq 

        p' : inj₁ y ∈P proj₁ resL
        p' = LAny.map (λ ·-≈P-inj₁y → DeltaPoset.Eq.sym P ·-≈P-inj₁y) p

        p'' : x ∈P proj₁ resL
        p'' = LAny.map (λ inj₁y-≈P-· → DeltaPoset.Eq.trans P x-≈P-inj₁y inj₁y-≈P-·) p'

    res-prop← x (inj₂ (y , x-≈P-inj₂y , y-∈R~fRaR)) rewrite concat-property = ∈-++⁺ʳ ≈P-setoid resL-list p''
      where
        open import Data.List.Membership.Setoid.Properties
        imp : ∀ {a : |P|} → {b : |R₀|} → (y ≈R₀ b) → (a ≡ inj₂ b) → (a ≈P inj₂ y)
        imp {a} {b} y-≈R₀-b a-≡-inj₂b = DeltaPoset.Eq.trans P a-≈P-inj₂b (₂∼₂ (≈R₀-sym y-≈R₀-b))  
          where
            open Setoid ≈P-setoid

            a-≈P-inj₂b : a ≈P inj₂ b
            a-≈P-inj₂b = ≈P-reflexive a-≡-inj₂b

        p : Any (λ · → · ≈P inj₂ y) resR-list
        p = pointwiseRespAny imp (proj₁ $ |fR| aR) resR-list y-∈R~fRaR resR-eq 

        p' : inj₂ y ∈P proj₁ resR
        p' = LAny.map (λ ·-≈P-inj₁y → DeltaPoset.Eq.sym P ·-≈P-inj₁y) p

        p'' : x ∈P proj₁ resR
        p'' = LAny.map (λ inj₂y-≈P-· → DeltaPoset.Eq.trans P x-≈P-inj₂y inj₂y-≈P-·) p'


    res-prop→ : ∀ (x : |P|) → x ∈P res →  
                   (Σ[ y ∈ |L₀| ] (x ≈P inj₁ y) × (y ∈L |fL| aL)) ⊎
                   (Σ[ y ∈ |R₀| ] (x ≈P inj₂ y) × (y ∈R |fR| aR))
    res-prop→ x x∈res with x∈resL⊎resR
      where
        open import Data.List.Membership.Setoid.Properties
        x∈resL⊎resR : x ∈P (proj₁ resL) ⊎ x ∈P (proj₁ resR)
        x∈resL⊎resR = ∈-++⁻ ≈P-setoid resL-list (PE.subst (λ z → x ∈P' z) concat-property x∈res)
    res-prop→ x x∈res | (inj₁ x∈resL) = inj₁ $ anyEliminate (proj₁ $ |fL| aL) elim p
      where
        imp : ∀ {a : |P|} → {b : |L₀|} → (x ≈P a) → (a ≡ inj₁ b) → (x ≈P inj₁ b)
        imp {a} {b} x≈a a≡inj₁b = PE.subst (λ · → x ≈P ·) a≡inj₁b x≈a 

        p : Any (λ · → x ≈P inj₁ ·) (proj₁ $ |fL| aL)
        p = pointwiseRespAny⃖ imp (proj₁ $ |fL| aL) resL-list x∈resL resL-eq

        elim : AnyEliminator {ℓQ = l0} |L₀| (Σ[ y ∈ |L₀| ] (x ≈P inj₁ y) × (y ∈L |fL| aL)) (λ · → x ≈P inj₁ ·) (proj₁ $ |fL| aL) 
        elim a f x≈Pa a∈≡fLaL = (a , x≈Pa , LAny.map (λ a∈≡· → ≈L₀-reflexive a∈≡·) a∈≡fLaL)
    res-prop→ x x∈res | (inj₂ x∈resR) = inj₂ $ anyEliminate (proj₁ $ |fR| aR) elim p
      where
        imp : ∀ {a : |P|} → {b : |R₀|} → (x ≈P a) → (a ≡ inj₂ b) → (x ≈P inj₂ b)
        imp {a} {b} x≈a a≡inj₂b = PE.subst (λ · → x ≈P ·) a≡inj₂b x≈a 

        p : Any (λ · → x ≈P inj₂ ·) (proj₁ $ |fR| aR)
        p = pointwiseRespAny⃖ imp (proj₁ $ |fR| aR) resR-list x∈resR resR-eq

        elim : AnyEliminator {ℓQ = l0} |R₀| (Σ[ y ∈ |R₀| ] (x ≈P inj₂ y) × (y ∈R |fR| aR)) (λ · → x ≈P inj₂ ·) (proj₁ $ |fR| aR) 
        elim a f x≈Pa a∈≡fRaR = (a , x≈Pa , LAny.map (λ a∈≡· → ≈R₀-reflexive a∈≡·) a∈≡fRaR)

    res-prop⇔ : (x : |P|) → (x ∈P res) ⇔ P-|f| (aL , aR) x
    res-prop⇔ x = equivalence (res-prop→ x) (res-prop← x)

--]]]

|f| : Carrier' → Carrier-FP
|f| c = proj₁ $ |f|-aux c

|f|-prop : (c : Carrier') → (x : |P|) → (x ∈P (|f| c)) ⇔ (P-|f| c x)
|f|-prop c = proj₂ $ |f|-aux c

|f|-≈ : (c1 c2 : Carrier') → c1 ≈' c2 → (|f| c1) ≈F (|f| c2)
--[[[
|f|-≈ (l1 , r1) (l2 , r2) (l1≈l2 , r1≈r2) = from ⟨$⟩ sameElements
  where
    p→ : (p : |P|) → (p ∈P (|f| $ l1 , r1)) → (p ∈P (|f| $ l2 , r2))
    --[[[
    p→ p p∈fc1 with to ⟨$⟩ p∈fc1
      where
        open Equivalence (|f|-prop (l1 , r1) p)
    p→ p p∈fc1 | inj₁ (l₀ , p≈inj₁l₀ , l₀∈fLl1) = 
      E3.from ⟨$⟩ inj₁ (l₀ , p≈inj₁l₀ , l₀∈fLl2) 
      where
        open import Data.List.Membership.Setoid.Properties
        module E1 = Equivalence (c1≈c2⇔sameElementsL (|fL| l1) (|fL| l2))
        module E2 = Equivalence ((E1.to ⟨$⟩ |fL|-≈ l1 l2 l1≈l2) l₀)

        l₀∈fLl2 : l₀ ∈L (|fL| l2)
        l₀∈fLl2 = E2.to ⟨$⟩ l₀∈fLl1

        module E3 = Equivalence (|f|-prop (l2 , r2) p)
    p→ p p∈fc1 | inj₂ (r₀ , p≈inj₂r₀ , r₀∈fRr1) =    
      E3.from ⟨$⟩ inj₂ (r₀ , p≈inj₂r₀ , r₀∈fRr2) 
      where
        open import Data.List.Membership.Setoid.Properties
        module E1 = Equivalence (c1≈c2⇔sameElementsR (|fR| r1) (|fR| r2))
        module E2 = Equivalence ((E1.to ⟨$⟩ |fR|-≈ r1 r2 r1≈r2) r₀)

        r₀∈fRr2 : r₀ ∈R (|fR| r2)
        r₀∈fRr2 = E2.to ⟨$⟩ r₀∈fRr1

        module E3 = Equivalence (|f|-prop (l2 , r2) p)
    --]]]

    p← : (p : |P|) → (p ∈P (|f| $ l2 , r2)) → (p ∈P (|f| $ l1 , r1))
    --[[[
    p← p p∈fc2 with to ⟨$⟩ p∈fc2
      where
        open Equivalence (|f|-prop (l2 , r2) p)
    p← p p∈fc2 | inj₁ (l₀ , p≈inj₁l₀ , l₀∈fLl2) = 
      E3.from ⟨$⟩ inj₁ (l₀ , p≈inj₁l₀ , l₀∈fLl1) 
      where
        open import Data.List.Membership.Setoid.Properties
        module E1 = Equivalence (c1≈c2⇔sameElementsL (|fL| l1) (|fL| l2))
        module E2 = Equivalence ((E1.to ⟨$⟩ |fL|-≈ l1 l2 l1≈l2) l₀)

        l₀∈fLl1 : l₀ ∈L (|fL| l1)
        l₀∈fLl1 = E2.from ⟨$⟩ l₀∈fLl2

        module E3 = Equivalence (|f|-prop (l1 , r1) p)
    p← p p∈fc2 | inj₂ (r₀ , p≈inj₂r₀ , r₀∈fRr2) =    
      E3.from ⟨$⟩ inj₂ (r₀ , p≈inj₂r₀ , r₀∈fRr1) 
      where
        open import Data.List.Membership.Setoid.Properties
        module E1 = Equivalence (c1≈c2⇔sameElementsR (|fR| r1) (|fR| r2))
        module E2 = Equivalence ((E1.to ⟨$⟩ |fR|-≈ r1 r2 r1≈r2) r₀)

        r₀∈fRr1 : r₀ ∈R (|fR| r1)
        r₀∈fRr1 = E2.from ⟨$⟩ r₀∈fRr2

        module E3 = Equivalence (|f|-prop (l1 , r1) p)
    --]]]

    sameElements : (p : |P|) → (p ∈P (|f| $ l1 , r1)) ⇔ (p ∈P (|f| $ l2 , r2))
    sameElements p = equivalence (p→ p) (p← p)

    open Equivalence (c1≈c2⇔sameElementsP (|f| $ l1 , r1) (|f| $ l2 , r2))
--]]]

|f|-⊥ : (|f| ⊥') ≈F ⊥F
--[[[
|f|-⊥ = from ⟨$⟩ sameElements
  where
    p→ : (p : |P|) → (p ∈P (|f| ⊥')) → (p ∈P ⊥F)
    --[[[
    p→ p p∈f⊥ with to ⟨$⟩ p∈f⊥
      where
        open Equivalence (|f|-prop ⊥' p)
    p→ p p∈f⊥ | inj₁ (l₀ , p≈inj₁l₀ , l₀∈fL⊥L) =
      ⊥-elim $ ¬Any[] l₀∈⊥FL
      where
        open import Data.List.Any.Properties

        module E1 = Equivalence (c1≈c2⇔sameElementsL (|fL| ⊥L) ⊥FL)
        module E2 = Equivalence ((E1.to ⟨$⟩ |fL|-⊥) l₀)

        l₀∈⊥FL : l₀ ∈L ⊥FL
        l₀∈⊥FL = E2.to ⟨$⟩ l₀∈fL⊥L
    p→ p p∈f⊥ | inj₂ (r₀ , p≈inj₂r₀ , r₀∈fR⊥R) =
      ⊥-elim $ ¬Any[] r₀∈⊥FR
      where
        open import Data.List.Any.Properties

        module E1 = Equivalence (c1≈c2⇔sameElementsR (|fR| ⊥R) ⊥FR)
        module E2 = Equivalence ((E1.to ⟨$⟩ |fR|-⊥) r₀)

        r₀∈⊥FR : r₀ ∈R ⊥FR
        r₀∈⊥FR = E2.to ⟨$⟩ r₀∈fR⊥R
    --]]]

    p← : (p : |P|) → (p ∈P ⊥F) → (p ∈P (|f| ⊥'))
    --[[[
    p← p p∈⊥F = ⊥-elim $ ¬Any[] p∈⊥F
      where
        open import Data.List.Any.Properties
    --]]]

    sameElements : (p : |P|) → (p ∈P (|f| ⊥')) ⇔ (p ∈P ⊥F)
    sameElements p = equivalence (p→ p) (p← p)

    open Equivalence (c1≈c2⇔sameElementsP (|f| ⊥') ⊥F)
--]]]

-- there's a lot of repitition in here. it shouldn't be hard to refactor it.
|f|-∨ : (a b : Carrier') → (|f| $ a ∨' b) ≈F ((|f| a) ∨F (|f| b))
--[[[
|f|-∨ a@(aL , aR) b@(bL , bR) = ≈F-sym {(|f| a) ∨F (|f| b)} {|f| $ a ∨' b} (ERES.from ⟨$⟩ sameElements)
  where
    module ERES = Equivalence (c1≈c2⇔sameElementsP ((|f| a) ∨F (|f| b)) (|f| $ a ∨' b))

    p→ : (p : |P|) → (p ∈P (|f| $ a ∨' b)) → (p ∈P ((|f| a) ∨F (|f| b)))
    --[[[

    p→ p p∈a∨b with to ⟨$⟩ p∈a∨b
      where
        open Equivalence (|f|-prop (a ∨' b) p)
    p→ (inj₁ p') p∈a∨b | inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fL-aL∨bL) with to ⟨$⟩ l₀∈fLaL∨fLbL
      where
        l₀∈fLaL∨fLbL : l₀ ∈L ((|fL| aL) ∨FL (|fL| bL))
        l₀∈fLaL∨fLbL = 
          p∈c1≈c2-L {p = l₀} {c1 = |fL| $ aL ∨L bL} {c2 = (|fL| aL) ∨FL (|fL| bL)} (|fL|-∨ aL bL) l₀∈fL-aL∨bL 

        open Equivalence (x∈∨⇔P∨-L (|fL| aL) (|fL| bL) ((|fL| aL) ∨FL (|fL| bL)) (LPW.refl ≈L₀-refl) l₀)
    p→ p@(inj₁ p') p∈a∨b | inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fL-aL∨bL) | inj₁ (l₀∈fLaL , ¬l₀⊑fLbL) = 
      E.from ⟨$⟩ inj₁ (p∈fa , ¬p⊑fb)
      where
        module E = Equivalence (x∈∨⇔P∨-P (|f| a) (|f| b) ((|f| a) ∨F (|f| b)) (≈F-refl {(|f| a) ∨F (|f| b)}) p)

        p∈fa : p ∈P (|f| a)
        p∈fa = from ⟨$⟩ inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fLaL) 
          where
            open Equivalence (|f|-prop a p)

        ¬p⊑fb : ¬ Any (p ⊑P_) (proj₁ $ |f| b)
        ¬p⊑fb p⊑fb = anyEliminate (proj₁ $ |f| b) elim p⊑fb
          where
            elim : AnyEliminator {ℓQ = l0} |P| ⊥ (p ⊑P_) (proj₁ $ |f| b)
            elim (inj₂ x') f (₁∼₂ ()) x∈fb
            elim (inj₁ x') f (₁∼₁ p'⊑x') x∈fb = ¬l₀⊑fLbL l₀⊑fLbL 
              where
                open Equivalence (|f|-prop b (inj₁ x'))

                l₀⊑fLbL : Any (l₀ ⊑L₀_) (proj₁ $ |fL| bL)
                l₀⊑fLbL with to ⟨$⟩ (LAny.map ≈P-reflexive x∈fb)
                l₀⊑fLbL | inj₁ (l₀' , (₁∼₁ x'≈l₀') , l₀'∈fLbL) = 
                  LAny.map (λ l₀'≈· → ⊑L₀-respʳ-≈L₀ l₀'≈· l₀⊑l₀') l₀'∈fLbL 
                  where
                    l₀⊑l₀' : l₀ ⊑L₀ l₀'
                    l₀⊑l₀' = ⊑L₀-trans (⊑L₀-reflexive $ ≈L₀-sym p'≈l₀) (⊑L₀-trans p'⊑x' (⊑L₀-reflexive x'≈l₀'))
                l₀⊑fLbL | inj₂ (r₀' , (₁∼₂ ()) , r₀'∈fRbR)
    p→ p@(inj₁ p') p∈a∨b | inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fL-aL∨bL) | inj₂ (inj₁ (l₀∈fLbL , ¬l₀⊑fLaL)) =
      E.from ⟨$⟩ inj₂ (inj₁ $  p∈fb , ¬p⊑fa)
      where
        module E = Equivalence (x∈∨⇔P∨-P (|f| a) (|f| b) ((|f| a) ∨F (|f| b)) (≈F-refl {(|f| a) ∨F (|f| b)}) p)

        p∈fb : p ∈P (|f| b)
        p∈fb = from ⟨$⟩ inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fLbL) 
          where
            open Equivalence (|f|-prop b p)

        ¬p⊑fa : ¬ Any (p ⊑P_) (proj₁ $ |f| a)
        ¬p⊑fa p⊑fa = anyEliminate (proj₁ $ |f| a) elim p⊑fa
          where
            elim : AnyEliminator {ℓQ = l0} |P| ⊥ (p ⊑P_) (proj₁ $ |f| a)
            elim (inj₂ x') f (₁∼₂ ()) x∈fa
            elim (inj₁ x') f (₁∼₁ p'⊑x') x∈fa = ¬l₀⊑fLaL l₀⊑fLaL 
              where
                open Equivalence (|f|-prop a (inj₁ x'))

                l₀⊑fLaL : Any (l₀ ⊑L₀_) (proj₁ $ |fL| aL)
                l₀⊑fLaL with to ⟨$⟩ (LAny.map ≈P-reflexive x∈fa)
                l₀⊑fLaL | inj₁ (l₀' , (₁∼₁ x'≈l₀') , l₀'∈fLaL) = 
                  LAny.map (λ l₀'≈· → ⊑L₀-respʳ-≈L₀ l₀'≈· l₀⊑l₀') l₀'∈fLaL 
                  where
                    l₀⊑l₀' : l₀ ⊑L₀ l₀'
                    l₀⊑l₀' = ⊑L₀-trans (⊑L₀-reflexive $ ≈L₀-sym p'≈l₀) (⊑L₀-trans p'⊑x' (⊑L₀-reflexive x'≈l₀'))
                l₀⊑fLaL | inj₂ (r₀' , (₁∼₂ ()) , r₀'∈fRbR)
    p→ p@(inj₁ p') p∈a∨b | inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fL-aL∨bL) | inj₂ (inj₂ (l₀∈fLaL , l₀∈fLbL)) =
      E.from ⟨$⟩ inj₂ (inj₂ $ p∈fa , p∈fb) 
      where
        module E = Equivalence (x∈∨⇔P∨-P (|f| a) (|f| b) ((|f| a) ∨F (|f| b)) (≈F-refl {(|f| a) ∨F (|f| b)}) p)

        p∈fa : p ∈P (|f| a)
        p∈fa = from ⟨$⟩ inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fLaL) 
          where
            open Equivalence (|f|-prop a p)

        p∈fb : p ∈P (|f| b)
        p∈fb = from ⟨$⟩ inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fLbL) 
          where
            open Equivalence (|f|-prop b p)
    p→ p@(inj₁ p') p∈a∨b | inj₂ (l₀ , (₁∼₂ ()) , l₀∈fL-aL∨bL)
    p→ p@(inj₂ p') p∈a∨b | inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fR-aR∨bR) with to ⟨$⟩ r₀∈fRaR∨fRbR
      where
        r₀∈fRaR∨fRbR : r₀ ∈R ((|fR| aR) ∨FR (|fR| bR))
        r₀∈fRaR∨fRbR = 
          p∈c1≈c2-R {p = r₀} {c1 = |fR| $ aR ∨R bR} {c2 = (|fR| aR) ∨FR (|fR| bR)} (|fR|-∨ aR bR) r₀∈fR-aR∨bR 

        open Equivalence (x∈∨⇔P∨-R (|fR| aR) (|fR| bR) ((|fR| aR) ∨FR (|fR| bR)) (LPW.refl ≈R₀-refl) r₀)
    p→ p@(inj₂ p') p∈a∨b | inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fR-aR∨bR) | inj₁ (r₀∈fRaR , ¬r₀⊑fRbR) =
      E.from ⟨$⟩ inj₁ (p∈fa , ¬p⊑fb)
      where
        module E = Equivalence (x∈∨⇔P∨-P (|f| a) (|f| b) ((|f| a) ∨F (|f| b)) (≈F-refl {(|f| a) ∨F (|f| b)}) p)

        p∈fa : p ∈P (|f| a)
        p∈fa = from ⟨$⟩ inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fRaR) 
          where
            open Equivalence (|f|-prop a p)

        ¬p⊑fb : ¬ Any (p ⊑P_) (proj₁ $ |f| b)
        ¬p⊑fb p⊑fb = anyEliminate (proj₁ $ |f| b) elim p⊑fb
          where
            elim : AnyEliminator {ℓQ = l0} |P| ⊥ (p ⊑P_) (proj₁ $ |f| b)
            elim (inj₂ x') f (₂∼₂ p'⊑x') x∈fb = ¬r₀⊑fRbR r₀⊑fRbR
              where
                open Equivalence (|f|-prop b (inj₂ x'))

                r₀⊑fRbR : Any (r₀ ⊑R₀_) (proj₁ $ |fR| bR)
                r₀⊑fRbR with to ⟨$⟩ (LAny.map ≈P-reflexive x∈fb)
                r₀⊑fRbR | inj₁ (l₀' , () , l₀'∈fLbL)
                r₀⊑fRbR | inj₂ (r₀' , (₂∼₂ x'≈r₀') , r₀'∈fRbR) = 
                  LAny.map (λ r₀'≈· → ⊑R₀-respʳ-≈R₀ r₀'≈· r₀⊑r₀') r₀'∈fRbR 
                  where
                    r₀⊑r₀' : r₀ ⊑R₀ r₀'
                    r₀⊑r₀' = ⊑R₀-trans (⊑R₀-reflexive $ ≈R₀-sym p'≈r₀) (⊑R₀-trans p'⊑x' (⊑R₀-reflexive x'≈r₀'))
    p→ p@(inj₂ p') p∈a∨b | inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fR-aR∨bR) | inj₂ (inj₁ (r₀∈fRbR , ¬r₀⊑fRaR)) =
      E.from ⟨$⟩ inj₂ (inj₁ $ p∈fb , ¬p⊑fa)
      where
        module E = Equivalence (x∈∨⇔P∨-P (|f| a) (|f| b) ((|f| a) ∨F (|f| b)) (≈F-refl {(|f| a) ∨F (|f| b)}) p)

        p∈fb : p ∈P (|f| b)
        p∈fb = from ⟨$⟩ inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fRbR) 
          where
            open Equivalence (|f|-prop b p)

        ¬p⊑fa : ¬ Any (p ⊑P_) (proj₁ $ |f| a)
        ¬p⊑fa p⊑fa = anyEliminate (proj₁ $ |f| a) elim p⊑fa
          where
            elim : AnyEliminator {ℓQ = l0} |P| ⊥ (p ⊑P_) (proj₁ $ |f| a)
            elim (inj₂ x') f (₂∼₂ p'⊑x') x∈fa = ¬r₀⊑fRaR r₀⊑fRaR
              where
                open Equivalence (|f|-prop a (inj₂ x'))

                r₀⊑fRaR : Any (r₀ ⊑R₀_) (proj₁ $ |fR| aR)
                r₀⊑fRaR with to ⟨$⟩ (LAny.map ≈P-reflexive x∈fa)
                r₀⊑fRaR | inj₁ (l₀' , () , l₀'∈fLaL)
                r₀⊑fRaR | inj₂ (r₀' , (₂∼₂ x'≈r₀') , r₀'∈fRaR) = 
                  LAny.map (λ r₀'≈· → ⊑R₀-respʳ-≈R₀ r₀'≈· r₀⊑r₀') r₀'∈fRaR 
                  where
                    r₀⊑r₀' : r₀ ⊑R₀ r₀'
                    r₀⊑r₀' = ⊑R₀-trans (⊑R₀-reflexive $ ≈R₀-sym p'≈r₀) (⊑R₀-trans p'⊑x' (⊑R₀-reflexive x'≈r₀'))
    p→ p@(inj₂ p') p∈a∨b | inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fR-aR∨bR) | inj₂ (inj₂ (r₀∈fRaR , r₀∈fRbR)) =
      E.from ⟨$⟩ inj₂ (inj₂ $ p∈fa , p∈fb)
      where
        module E = Equivalence (x∈∨⇔P∨-P (|f| a) (|f| b) ((|f| a) ∨F (|f| b)) (≈F-refl {(|f| a) ∨F (|f| b)}) p)

        p∈fa : p ∈P (|f| a)
        p∈fa = from ⟨$⟩ inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fRaR) 
          where
            open Equivalence (|f|-prop a p)

        p∈fb : p ∈P (|f| b)
        p∈fb = from ⟨$⟩ inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fRbR) 
          where
            open Equivalence (|f|-prop b p)
    p→ (inj₂ p') p∈a∨b | inj₁ (r₀ , () , r₀∈fR-aR∨bR)

    --]]]

    p← : (p : |P|) → (p ∈P ((|f| a) ∨F (|f| b))) → (p ∈P (|f| $ a ∨' b))
    --[[[
    -- there's a lot of repitition in here. it shouldn't be hard to refactor it.
    p← p p∈fa∨fb with to ⟨$⟩ p∈fa∨fb
      where 
        open Equivalence (x∈∨⇔P∨-P (|f| a) (|f| b) ((|f| a) ∨F (|f| b)) (≈F-refl {(|f| a) ∨F (|f| b)}) p)
    p← p p∈fa∨fb | inj₁ (p∈fa , ¬p⊑fb) with to ⟨$⟩ p∈fa
      where
        open Equivalence (|f|-prop a p)
    p← p@(inj₁ p') p∈fa∨fb | inj₁ (p∈fa , ¬p⊑fb) | inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fLaL) = 
      ∈-resp-≈ ≈P-setoid (₁∼₁ $ ≈L₀-sym p'≈l₀) inj₁l₀∈f-a∨b
      where
        open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)

        l₀∈fLaL∨fLbL : l₀ ∈L ((|fL| aL) ∨FL (|fL| bL))
        --[[[
        l₀∈fLaL∨fLbL = from ⟨$⟩ (inj₁ $ l₀∈fLaL , ¬l₀⊑fLbL) 
          where
            open Equivalence (x∈∨⇔P∨-L (|fL| aL) (|fL| bL) ((|fL| aL) ∨FL (|fL| bL)) (LPW.refl ≈L₀-refl) l₀)

            ¬l₀⊑fLbL : ¬ Any (l₀ ⊑L₀_) (proj₁ $ |fL| bL)
            ¬l₀⊑fLbL l₀⊑fLbL = anyEliminate (proj₁ $ |fL| bL) elim l₀⊑fLbL 
              where
                elim : AnyEliminator {ℓQ = l0} |L₀| ⊥ (l₀ ⊑L₀_) (proj₁ $ |fL| bL)
                elim x f l₀⊑x x∈fLbL = 
                  ⊥-elim $ ¬p⊑fb (LAny.map (λ inj₁x≈· → ⊑P-trans p⊑inj₁x (⊑P-reflexive inj₁x≈·)) inj₁x∈fb) 
                  where
                    module EFB = Equivalence (|f|-prop b (inj₁ x))

                    inj₁x∈fb : (inj₁ x) ∈P (|f| b)
                    inj₁x∈fb = EFB.from ⟨$⟩ inj₁ (x , ≈P-refl , (LAny.map ≈L₀-reflexive x∈fLbL))

                    p⊑inj₁x : p ⊑P (inj₁ x)
                    p⊑inj₁x = ₁∼₁ (⊑L₀-trans (⊑L₀-reflexive p'≈l₀) l₀⊑x)
          --]]]
        l₀∈fL-aL∨bL : l₀ ∈L (|fL| $ aL ∨L bL)
        --[[[
        l₀∈fL-aL∨bL = 
          p∈c1≈c2-L {l₀} {(|fL| aL) ∨FL (|fL| bL)} {|fL| $ aL ∨L bL} 
                     (≈FL-sym {|fL| $ aL ∨L bL} {(|fL| aL) ∨FL (|fL| bL)} (|fL|-∨ aL bL)) l₀∈fLaL∨fLbL 
        --]]]
        inj₁l₀∈f-a∨b : (inj₁ l₀) ∈P (|f| $ a ∨' b)
        --[[[
        inj₁l₀∈f-a∨b = from ⟨$⟩ (inj₁ $ l₀ , ≈P-refl , l₀∈fL-aL∨bL)
          where
            open Equivalence (|f|-prop (a ∨' b) (inj₁ l₀))
        --]]]
    p← p@(inj₁ p') p∈fa∨fb | inj₁ (p∈fa , ¬p⊑fb) | inj₂ (r₀ , (₁∼₂ ()) , r₀∈fRaR)
    p← p@(inj₂ p') p∈fa∨fb | inj₁ (p∈fa , ¬p⊑fb) | inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fRaR) = 
      ∈-resp-≈ ≈P-setoid (₂∼₂ $ ≈R₀-sym p'≈r₀) inj₂r₀∈f-a∨b
      where
        open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)

        r₀∈fRaR∨fRbR : r₀ ∈R ((|fR| aR) ∨FR (|fR| bR))
        --[[[
        r₀∈fRaR∨fRbR = from ⟨$⟩ (inj₁ $ r₀∈fRaR , ¬r₀⊑fRbR) 
          where
            open Equivalence (x∈∨⇔P∨-R (|fR| aR) (|fR| bR) ((|fR| aR) ∨FR (|fR| bR)) (LPW.refl ≈R₀-refl) r₀)

            ¬r₀⊑fRbR : ¬ Any (r₀ ⊑R₀_) (proj₁ $ |fR| bR)
            ¬r₀⊑fRbR r₀⊑fRbR = anyEliminate (proj₁ $ |fR| bR) elim r₀⊑fRbR 
              where
                elim : AnyEliminator {ℓQ = l0} |R₀| ⊥ (r₀ ⊑R₀_) (proj₁ $ |fR| bR)
                elim x f r₀⊑x x∈fRbR = 
                  ⊥-elim $ ¬p⊑fb (LAny.map (λ inj₂x≈· → ⊑P-trans p⊑inj₂x (⊑P-reflexive inj₂x≈·)) inj₂x∈fb) 
                  where
                    module EFB = Equivalence (|f|-prop b (inj₂ x))

                    inj₂x∈fb : (inj₂ x) ∈P (|f| b)
                    inj₂x∈fb = EFB.from ⟨$⟩ inj₂ (x , ≈P-refl , (LAny.map ≈R₀-reflexive x∈fRbR))

                    p⊑inj₂x : p ⊑P (inj₂ x)
                    p⊑inj₂x = ₂∼₂ (⊑R₀-trans (⊑R₀-reflexive p'≈r₀) r₀⊑x)
          --]]]
        r₀∈fR-aR∨bR : r₀ ∈R (|fR| $ aR ∨R bR)
        --[[[
        r₀∈fR-aR∨bR = 
          p∈c1≈c2-R {r₀} {(|fR| aR) ∨FR (|fR| bR)} {|fR| $ aR ∨R bR} 
                     (≈FR-sym {|fR| $ aR ∨R bR} {(|fR| aR) ∨FR (|fR| bR)} (|fR|-∨ aR bR)) r₀∈fRaR∨fRbR 
        --]]]
        inj₂r₀∈f-a∨b : (inj₂ r₀) ∈P (|f| $ a ∨' b)
        --[[[
        inj₂r₀∈f-a∨b = from ⟨$⟩ (inj₂ $ r₀ , ≈P-refl , r₀∈fR-aR∨bR)
          where
            open Equivalence (|f|-prop (a ∨' b) (inj₂ r₀))
        --]]]
    p← p@(inj₂ p') p∈fa∨fb | inj₁ (p∈fa , ¬p⊑fb) | inj₁ (l₀ , () , l₀∈fLaL)

    p← p p∈fa∨fb | inj₂ (inj₁ (p∈fb , ¬p⊑fa)) with to ⟨$⟩ p∈fb
      where
        open Equivalence (|f|-prop b p)
    p← p@(inj₁ p') p∈fa∨fb | inj₂ (inj₁ (p∈fb , ¬p⊑fa)) | inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fLbL) = 
      ∈-resp-≈ ≈P-setoid (₁∼₁ $ ≈L₀-sym p'≈l₀) inj₁l₀∈f-a∨b
      where
        open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)

        l₀∈fLaL∨fLbL : l₀ ∈L ((|fL| aL) ∨FL (|fL| bL))
        --[[[
        l₀∈fLaL∨fLbL = from ⟨$⟩ (inj₂ $ inj₁ $ l₀∈fLbL , ¬l₀⊑fLaL) 
          where
            open Equivalence (x∈∨⇔P∨-L (|fL| aL) (|fL| bL) ((|fL| aL) ∨FL (|fL| bL)) (LPW.refl ≈L₀-refl) l₀)

            ¬l₀⊑fLaL : ¬ Any (l₀ ⊑L₀_) (proj₁ $ |fL| aL)
            ¬l₀⊑fLaL l₀⊑fLaL = anyEliminate (proj₁ $ |fL| aL) elim l₀⊑fLaL 
              where
                elim : AnyEliminator {ℓQ = l0} |L₀| ⊥ (l₀ ⊑L₀_) (proj₁ $ |fL| aL)
                elim x f l₀⊑x x∈fLbL = 
                  ⊥-elim $ ¬p⊑fa (LAny.map (λ inj₁x≈· → ⊑P-trans p⊑inj₁x (⊑P-reflexive inj₁x≈·)) inj₁x∈fa) 
                  where
                    module EFA = Equivalence (|f|-prop a (inj₁ x))

                    inj₁x∈fa : (inj₁ x) ∈P (|f| a)
                    inj₁x∈fa = EFA.from ⟨$⟩ inj₁ (x , ≈P-refl , (LAny.map ≈L₀-reflexive x∈fLbL))

                    p⊑inj₁x : p ⊑P (inj₁ x)
                    p⊑inj₁x = ₁∼₁ (⊑L₀-trans (⊑L₀-reflexive p'≈l₀) l₀⊑x)
          --]]]
        l₀∈fL-aL∨bL : l₀ ∈L (|fL| $ aL ∨L bL)
        --[[[
        l₀∈fL-aL∨bL = 
          p∈c1≈c2-L {l₀} {(|fL| aL) ∨FL (|fL| bL)} {|fL| $ aL ∨L bL} 
                     (≈FL-sym {|fL| $ aL ∨L bL} {(|fL| aL) ∨FL (|fL| bL)} (|fL|-∨ aL bL)) l₀∈fLaL∨fLbL 
        --]]]
        inj₁l₀∈f-a∨b : (inj₁ l₀) ∈P (|f| $ a ∨' b)
        --[[[
        inj₁l₀∈f-a∨b = from ⟨$⟩ (inj₁ $ l₀ , ≈P-refl , l₀∈fL-aL∨bL)
          where
            open Equivalence (|f|-prop (a ∨' b) (inj₁ l₀))
        --]]]
    p← p@(inj₁ p') p∈fa∨fb | inj₂ (inj₁ (p∈fb , ¬p⊑fa)) | inj₂ (r₀ , (₁∼₂ ()) , r₀∈fRbR)
    p← p@(inj₂ p') p∈fa∨fb | inj₂ (inj₁ (p∈fb , ¬p⊑fa)) | inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fRbR) = 
      ∈-resp-≈ ≈P-setoid (₂∼₂ $ ≈R₀-sym p'≈r₀) inj₂r₀∈f-a∨b
      where
        open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)

        r₀∈fRaR∨fRbR : r₀ ∈R ((|fR| aR) ∨FR (|fR| bR))
        --[[[
        r₀∈fRaR∨fRbR = from ⟨$⟩ (inj₂ $ inj₁ $ r₀∈fRbR , ¬r₀⊑fRaR) 
          where
            open Equivalence (x∈∨⇔P∨-R (|fR| aR) (|fR| bR) ((|fR| aR) ∨FR (|fR| bR)) (LPW.refl ≈R₀-refl) r₀)

            ¬r₀⊑fRaR : ¬ Any (r₀ ⊑R₀_) (proj₁ $ |fR| aR)
            ¬r₀⊑fRaR r₀⊑fRaR = anyEliminate (proj₁ $ |fR| aR) elim r₀⊑fRaR 
              where
                elim : AnyEliminator {ℓQ = l0} |R₀| ⊥ (r₀ ⊑R₀_) (proj₁ $ |fR| aR)
                elim x f r₀⊑x x∈fRaR = 
                  ⊥-elim $ ¬p⊑fa (LAny.map (λ inj₂x≈· → ⊑P-trans p⊑inj₂x (⊑P-reflexive inj₂x≈·)) inj₂x∈fa) 
                  where
                    module EFB = Equivalence (|f|-prop a (inj₂ x))

                    inj₂x∈fa : (inj₂ x) ∈P (|f| a)
                    inj₂x∈fa = EFB.from ⟨$⟩ inj₂ (x , ≈P-refl , (LAny.map ≈R₀-reflexive x∈fRaR))

                    p⊑inj₂x : p ⊑P (inj₂ x)
                    p⊑inj₂x = ₂∼₂ (⊑R₀-trans (⊑R₀-reflexive p'≈r₀) r₀⊑x)
          --]]]
        r₀∈fR-aR∨bR : r₀ ∈R (|fR| $ aR ∨R bR)
        --[[[
        r₀∈fR-aR∨bR = 
          p∈c1≈c2-R {r₀} {(|fR| aR) ∨FR (|fR| bR)} {|fR| $ aR ∨R bR} 
                     (≈FR-sym {|fR| $ aR ∨R bR} {(|fR| aR) ∨FR (|fR| bR)} (|fR|-∨ aR bR)) r₀∈fRaR∨fRbR 
        --]]]
        inj₂r₀∈f-a∨b : (inj₂ r₀) ∈P (|f| $ a ∨' b)
        --[[[
        inj₂r₀∈f-a∨b = from ⟨$⟩ (inj₂ $ r₀ , ≈P-refl , r₀∈fR-aR∨bR)
          where
            open Equivalence (|f|-prop (a ∨' b) (inj₂ r₀))
        --]]]
    p← p@(inj₂ p') p∈fa∨fb | inj₂ (inj₁ (p∈fa , ¬p⊑fb)) | inj₁ (l₀ , () , l₀∈fLbL)
    p← p p∈fa∨fb | inj₂ (inj₂ (p∈fa , p∈fb)) with EFA.to ⟨$⟩ p∈fa | EFB.to ⟨$⟩ p∈fb  
      where
        module EFA = Equivalence (|f|-prop a p)
        module EFB = Equivalence (|f|-prop b p)
    p← (inj₁ p') p∈fa∨fb | inj₂ (inj₂ (p∈fa , p∈fb)) | inj₁ (l₀ , (₁∼₁ p'≈l₀) , l₀∈fLaL) | inj₁ (l₀' , (₁∼₁ p'≈l₀') , l₀'∈fLbL) =
      ∈-resp-≈ ≈P-setoid (₁∼₁ $ ≈L₀-sym p'≈l₀) inj₁l₀∈f-a∨b
      where
        open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)

        l₀∈fLaL∨fLbL : l₀ ∈L ((|fL| aL) ∨FL (|fL| bL))
        --[[[
        l₀∈fLaL∨fLbL = 
          from ⟨$⟩ (inj₂ (inj₂ (l₀∈fLaL , ∈-resp-≈ ≈L₀-setoid (≈L₀-trans (≈L₀-sym p'≈l₀') p'≈l₀) l₀'∈fLbL))) 
          where
            open Equivalence (x∈∨⇔P∨-L (|fL| aL) (|fL| bL) ((|fL| aL) ∨FL (|fL| bL)) (LPW.refl ≈L₀-refl) l₀)
        --]]]
        l₀∈fL-aL∨bL : l₀ ∈L (|fL| (aL ∨L bL))
        --[[[
        l₀∈fL-aL∨bL = 
          p∈c1≈c2-L {l₀} {(|fL| aL) ∨FL (|fL| bL)} {|fL| (aL ∨L bL)} 
                     (≈FL-sym {|fL| (aL ∨L bL)} {(|fL| aL) ∨FL (|fL| bL)} (|fL|-∨ aL bL)) l₀∈fLaL∨fLbL 
        --]]]
        inj₁l₀∈f-a∨b : (inj₁ l₀) ∈P (|f| (a ∨' b))
        --[[[
        inj₁l₀∈f-a∨b = from ⟨$⟩ (inj₁ $ l₀ , ≈P-refl , l₀∈fL-aL∨bL)
          where
            open Equivalence (|f|-prop (a ∨' b) (inj₁ l₀))
        --]]]      
    p← (inj₁ p') p∈fa∨fb | inj₂ (inj₂ (p∈fa , p∈fb)) | inj₂ (r₀ , (₁∼₂ ()) , r₀∈fRaR) | _    
    p← (inj₁ p') p∈fa∨fb | inj₂ (inj₂ (p∈fa , p∈fb)) | _ | inj₂ (r₀ , (₁∼₂ ()) , r₀∈fRbR)
    p← (inj₂ p') p∈fa∨fb | inj₂ (inj₂ (p∈fa , p∈fb)) | inj₂ (r₀ , (₂∼₂ p'≈r₀) , r₀∈fRaR) | inj₂ (r₀' , (₂∼₂ p'≈r₀') , r₀'∈fRbR) =
      ∈-resp-≈ ≈P-setoid (₂∼₂ $ ≈R₀-sym p'≈r₀) inj₂r₀∈f-a∨b
      where
        open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)

        r₀∈fRaR∨fRbR : r₀ ∈R ((|fR| aR) ∨FR (|fR| bR))
        --[[[
        r₀∈fRaR∨fRbR = 
          from ⟨$⟩ (inj₂ (inj₂ $ r₀∈fRaR , (∈-resp-≈ ≈R₀-setoid (≈R₀-trans (≈R₀-sym p'≈r₀') p'≈r₀) r₀'∈fRbR))) 
          where
            open Equivalence (x∈∨⇔P∨-R (|fR| aR) (|fR| bR) ((|fR| aR) ∨FR (|fR| bR)) (LPW.refl ≈R₀-refl) r₀)
        --]]]
        r₀∈fR-aR∨bR : r₀ ∈R (|fR| (aR ∨R bR))
        --[[[
        r₀∈fR-aR∨bR = 
          p∈c1≈c2-R {r₀} {(|fR| aR) ∨FR (|fR| bR)} {|fR| (aR ∨R bR)} 
                     (≈FR-sym {|fR| (aR ∨R bR)} {(|fR| aR) ∨FR (|fR| bR)} (|fR|-∨ aR bR)) r₀∈fRaR∨fRbR 
        --]]]
        inj₂r₀∈f-a∨b : (inj₂ r₀) ∈P (|f| (a ∨' b))
        --[[[
        inj₂r₀∈f-a∨b = from ⟨$⟩ (inj₂ $ r₀ , ≈P-refl , r₀∈fR-aR∨bR)
          where
            open Equivalence (|f|-prop (a ∨' b) (inj₂ r₀))
        --]]]      
    p← (inj₂ p') p∈fa∨fb | inj₂ (inj₂ (p∈fa , p∈fb)) | inj₁ (l₀ , () , l₀∈fLaL) | _    
    p← (inj₂ p') p∈fa∨fb | inj₂ (inj₂ (p∈fa , p∈fb)) | _ | inj₁ (l₀ , () , l₀∈fLbL)
    --]]]

    sameElements : (p : |P|) → (p ∈P ((|f| a) ∨F (|f| b))) ⇔ (p ∈P (|f| $ a ∨' b))
    --[[[
    sameElements p = equivalence (p← p) (p→ p) 
    --]]]
--]]]

decompose' : (c : List |P|) → IsFreeList c →  
          Σ[ l ∈ Carrier-FPL ] Σ[ r ∈ Carrier-FPR ] Σ[ tl ∈ Carrier-FP ] Σ[ tr ∈ Carrier-FP ]
          LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ l) (proj₁ tl) ×
          LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ r) (proj₁ tr) ×
          c ≡ (proj₁ tl) ++ (proj₁ tr)
--[[[
decompose' [] []-Free = 
  ([] , []-FreeL) , 
  ([] , []-FreeR) , 
  ([] , []-Free) , 
  ([] , []-Free) , 
  [] , 
  [] ,
  ++-identityˡ []
  where
    open import Data.List.Properties
decompose' ((inj₁ h') ∷ t) (∷-Free .(inj₁ h') .t min incomp ft) =
   (h' ∷ (proj₁ restL) , ∷-FreeL h' (proj₁ restL) minL incompL (proj₂ restL)) , 
   restR , 
   (inj₁ h' ∷ (proj₁ restTL) , ∷-Free (inj₁ h') (proj₁ restTL) minTL incompTL (proj₂ restTL))  , 
   restTR , 
   PE.refl ∷ rest-eql , 
   rest-eqr , 
   PE.cong (λ · → inj₁ h' ∷ ·) rest-concat
  where
    rest : Σ[ l ∈ Carrier-FPL ] Σ[ r ∈ Carrier-FPR ] Σ[ tl ∈ Carrier-FP ] Σ[ tr ∈ Carrier-FP ]
           LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ l) (proj₁ tl) ×
           LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ r) (proj₁ tr) ×
           t ≡ (proj₁ tl) ++ (proj₁ tr)

    rest = decompose' t ft

    restL : Carrier-FPL
    restL = let l , _ , _ , _ , _ , _ , _ = rest in l

    restR : Carrier-FPR
    restR = let _ , r , _ , _ , _ , _ , _ = rest in r

    restTL : Carrier-FP
    restTL = let _ , _ , tl , _ , _ , _ , _ = rest in tl

    restTR : Carrier-FP
    restTR = let _ , _ , _ , tr , _ , _ , _ = rest in tr

    rest-eql : LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ restL) (proj₁ restTL)
    rest-eql = let _ , _ , _ , _ , eql , _ , _ = rest in eql

    rest-eqr : LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ restR) (proj₁ restTR)
    rest-eqr = let _ , _ , _ , _ , _ , eqr , _ = rest in eqr

    rest-concat : t ≡ (proj₁ restTL) ++ (proj₁ restTR)
    rest-concat = let _ , _ , _ , _ , _ , _ , conc = rest in conc

    minL : All (h' <L₀_) (proj₁ restL)
    minL =
      pointwiseRespAll⃖ imp (proj₁ restL) (proj₁ restTL) p' rest-eql
      where
        open import Data.List.All.Properties

        p : All (inj₁ h' <P_) ((proj₁ restTL) ++ (proj₁ restTR))
        p rewrite PE.sym rest-concat = min 

        p' : All (inj₁ h' <P_) (proj₁ restTL)
        p' = ++⁻ˡ (proj₁ restTL) p

        imp : {a : |L₀|} → {b : |P|} → (inj₁ h' <P b) → (b ≡ inj₁ a) → (h' <L₀ a)
        imp {a} {b} (₁∼₁ h'<a) b≡inj₁a@PE.refl = h'<a

    minTL : All (inj₁ h' <P_) (proj₁ restTL)
    minTL = ++⁻ˡ (proj₁ restTL) p
      where
        open import Data.List.All.Properties

        p : All (inj₁ h' <P_) ((proj₁ restTL) ++ (proj₁ restTR))
        p rewrite PE.sym rest-concat = min     

    incompL : ¬ Any (h' ∦L₀_) (proj₁ restL)
    incompL h'∦restL = ⊥-elim $ incomp p'
      where
        open import Data.List.Any.Properties

        imp : {a : |L₀|} → {b : |P|} → h' ∦L₀ a → b ≡ inj₁ a → (inj₁ h') ∦P b
        imp {a} {b} (inj₁ h'⊑a) b≡inj₁a@PE.refl = inj₁ (₁∼₁ h'⊑a)
        imp {a} {b} (inj₂ a⊑h') b≡inj₁a@PE.refl = inj₂ (₁∼₁ a⊑h')

        p : Any (inj₁ h' ∦P_) (proj₁ restTL)
        p = pointwiseRespAny imp (proj₁ restL) (proj₁ restTL) h'∦restL rest-eql

        p' : Any (inj₁ h' ∦P_) t
        p' = PE.subst (λ · → Any (inj₁ h' ∦P_) ·) (PE.sym rest-concat) (++⁺ˡ p) 

    incompTL : ¬ Any (inj₁ h' ∦P_) (proj₁ restTL)
    incompTL inj₁h'∦restTL = ⊥-elim $ incomp p'
      where
        open import Data.List.Any.Properties

        p' : Any (inj₁ h' ∦P_) t
        p' = PE.subst (λ · → Any (inj₁ h' ∦P_) ·) (PE.sym rest-concat) (++⁺ˡ inj₁h'∦restTL) 

decompose' ((inj₂ h') ∷ t) (∷-Free .(inj₂ h') .t min incomp ft) =
   restL ,
   (h' ∷ (proj₁ restR) , ∷-FreeR h' (proj₁ restR) minR incompR (proj₂ restR)) , 
   restTL ,
   (inj₂ h' ∷ (proj₁ restTR) , ∷-Free (inj₂ h') (proj₁ restTR) minTR incompTR (proj₂ restTR))  , 
   rest-eql ,
   PE.refl ∷ rest-eqr ,
   (begin
      inj₂ h' ∷ t ≡⟨ ++-identityˡ (inj₂ h' ∷ t) ⟩
      [] ++ (inj₂ h' ∷ t) ≡⟨ PE.cong (λ · → · ++ (inj₂ h' ∷ t)) $ PE.sym restTL-empty ⟩
      (proj₁ restTL) ++ (inj₂ h' ∷ t) ≡⟨ PE.cong (λ · → (proj₁ restTL) ++ (inj₂ h' ∷ ·)) rest-concat ⟩
      (proj₁ restTL) ++ (inj₂ h' ∷ (proj₁ restTL) ++ (proj₁ restTR)) ≡⟨ PE.cong (λ · → (proj₁ restTL) ++ (inj₂ h' ∷ (· ++ (proj₁ restTR)))) $ restTL-empty ⟩ 
      (proj₁ restTL) ++ (inj₂ h' ∷ [] ++ (proj₁ restTR)) ≡⟨ PE.cong (λ · → (proj₁ restTL) ++ (inj₂ h' ∷ ·)) $ ++-identityˡ (proj₁ restTR) ⟩ 
      (proj₁ restTL) ++ (inj₂ h' ∷ (proj₁ restTR)) 
     ∎) 
  where
    open PE.≡-Reasoning
    rest : Σ[ l ∈ Carrier-FPL ] Σ[ r ∈ Carrier-FPR ] Σ[ tl ∈ Carrier-FP ] Σ[ tr ∈ Carrier-FP ]
           LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ l) (proj₁ tl) ×
           LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ r) (proj₁ tr) ×
           t ≡ (proj₁ tl) ++ (proj₁ tr)

    rest = decompose' t ft

    restL : Carrier-FPL
    restL = let l , _ , _ , _ , _ , _ , _ = rest in l

    restR : Carrier-FPR
    restR = let _ , r , _ , _ , _ , _ , _ = rest in r

    restTL : Carrier-FP
    restTL = let _ , _ , tl , _ , _ , _ , _ = rest in tl

    restTR : Carrier-FP
    restTR = let _ , _ , _ , tr , _ , _ , _ = rest in tr

    rest-eql : LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ restL) (proj₁ restTL)
    rest-eql = let _ , _ , _ , _ , eql , _ , _ = rest in eql

    rest-eqr : LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ restR) (proj₁ restTR)
    rest-eqr = let _ , _ , _ , _ , _ , eqr , _ = rest in eqr

    rest-concat : t ≡ (proj₁ restTL) ++ (proj₁ restTR)
    rest-concat = let _ , _ , _ , _ , _ , _ , conc = rest in conc

    minTL : All (inj₂ h' <P_) (proj₁ restTL)
    minTL = ++⁻ˡ (proj₁ restTL) p
      where
        open import Data.List.All.Properties

        p : All (inj₂ h' <P_) ((proj₁ restTL) ++ (proj₁ restTR))
        p rewrite PE.sym rest-concat = min    


    restTL-empty : (proj₁ restTL) ≡ []
    restTL-empty with keep (proj₁ restTL)
    restTL-empty | ([]) , q = q
    restTL-empty | (inj₁ x' ∷ t) , q with p₁
      where
        p₀ : inj₁ x' ∈≡ proj₁ restTL
        p₀ rewrite q = here PE.refl 

        p₁ : inj₂ h' <P inj₁ x'
        p₁ = LA.lookup minTL {inj₁ x'} p₀
    restTL-empty | (inj₁ x' ∷ t) , q | ()
    restTL-empty | (inj₂ x' ∷ t) , q with pointwise∈⃖ (proj₁ restL) (proj₁ restTL) (inj₂ x') z rest-eql
      where
        z : inj₂ x' ∈≡ (proj₁ restTL)
        z rewrite q = here PE.refl
    restTL-empty | (inj₂ x' ∷ t) , q | b , inj₂x'≡inj₁b =
      ⊥-elim $ inj-clash b x' (PE.sym inj₂x'≡inj₁b)

    minR : All (h' <R₀_) (proj₁ restR)
    minR =
      pointwiseRespAll⃖ imp (proj₁ restR) (proj₁ restTR) p' rest-eqr
      where
        open import Data.List.All.Properties

        p : All (inj₂ h' <P_) ((proj₁ restTL) ++ (proj₁ restTR))
        p rewrite PE.sym rest-concat = min 

        p' : All (inj₂ h' <P_) (proj₁ restTR)
        p' = ++⁻ʳ (proj₁ restTL) p

        imp : {a : |R₀|} → {b : |P|} → (inj₂ h' <P b) → (b ≡ inj₂ a) → (h' <R₀ a)
        imp {a} {b} (₂∼₂ h'<a) b≡inj₂a@PE.refl = h'<a

    minTR : All (inj₂ h' <P_) (proj₁ restTR)
    minTR = ++⁻ʳ (proj₁ restTL) p
      where
        open import Data.List.All.Properties

        p : All (inj₂ h' <P_) ((proj₁ restTL) ++ (proj₁ restTR))
        p rewrite PE.sym rest-concat = min     

    incompR : ¬ Any (h' ∦R₀_) (proj₁ restR)
    incompR h'∦restR = ⊥-elim $ incomp p'
      where
        open import Data.List.Any.Properties

        imp : {a : |R₀|} → {b : |P|} → h' ∦R₀ a → b ≡ inj₂ a → (inj₂ h') ∦P b
        imp {a} {b} (inj₁ h'⊑a) b≡inj₁a@PE.refl = inj₁ (₂∼₂ h'⊑a)
        imp {a} {b} (inj₂ a⊑h') b≡inj₁a@PE.refl = inj₂ (₂∼₂ a⊑h')

        p : Any (inj₂ h' ∦P_) (proj₁ restTR)
        p = pointwiseRespAny imp (proj₁ restR) (proj₁ restTR) h'∦restR rest-eqr

        p' : Any (inj₂ h' ∦P_) t
        p' = PE.subst (λ · → Any (inj₂ h' ∦P_) ·) (PE.sym rest-concat) (++⁺ʳ (proj₁ restTL) p) 

    incompTR : ¬ Any (inj₂ h' ∦P_) (proj₁ restTR)
    incompTR inj₂h'∦restTR = ⊥-elim $ incomp p'
      where
        open import Data.List.Any.Properties

        p' : Any (inj₂ h' ∦P_) t
        p' = PE.subst (λ · → Any (inj₂ h' ∦P_) ·) (PE.sym rest-concat) (++⁺ʳ (proj₁ restTL) inj₂h'∦restTR) 
--]]]

decompose : (c : Carrier-FP) → 
          Σ[ l ∈ Carrier-FPL ] Σ[ r ∈ Carrier-FPR ] Σ[ tl ∈ Carrier-FP ] Σ[ tr ∈ Carrier-FP ]
          LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ l) (proj₁ tl) ×
          LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ r) (proj₁ tr) ×
          (proj₁ c) ≡ (proj₁ tl) ++ (proj₁ tr)
decompose (c , f) = decompose' c f 

decompL : Carrier-FP → Carrier-FPL
decompL a with decompose a
decompL a | l , r , tl , tr , eql , eqr , concat =
  l

decompR : Carrier-FP → Carrier-FPR
decompR a with decompose a
decompR a | l , r , tl , tr , eql , eqr , concat =
  r

|g| : Carrier-FP → Carrier'
--[[[

|g| c with decompose c
|g| c | l , r , tl , tr , eql , eqr , concat = 
  (|gL| l , |gR| r)

--]]]

|g|-≈ : (a b : Carrier-FP) → (a ≈F b) → (|g| a) ≈' (|g| b)
--[[[

|g|-≈ a b a≈b with decompose a | decompose b
|g|-≈ a@(.(proj₁ atl ++ proj₁ atr) , _) b@(.(proj₁ btl ++ proj₁ btr) , _) a≈b  
      | al , ar , atl , atr , aeql , aeqr , PE.refl 
      | bl , br , btl , btr , beql , beqr , PE.refl = 
  |gL|-≈ al bl al≈bl , |gR|-≈ ar br ar≈br
  where
    atl≈btl : atl ≈F btl
    --[[[
    atl≈btl with to ⟨$⟩ a≈b  
      where
        open Equivalence (c1≈c2⇔sameElementsP a b)
    atl≈btl | p∈a⇔p∈b =
      E.from ⟨$⟩ sameElements
      where
        p→ : (p : |P|) → (p ∈P atl) → (p ∈P btl)
        --[[[
        p→ p p∈atl = p∈btl 
          where
            open import Data.List.Membership.Setoid.Properties
            module E = Equivalence (p∈a⇔p∈b p) 

            p∈a : p ∈P a
            p∈a = ∈-++⁺ˡ ≈P-setoid p∈atl

            p∈b : p ∈P b
            p∈b = E.to ⟨$⟩ p∈a

            p∈btl : p ∈P btl
            p∈btl with ∈-++⁻ ≈P-setoid (proj₁ btl) p∈b
            p∈btl | inj₁ goal = goal
            p∈btl | inj₂ p∈btr = 
              ⊥-elim $ I1.from ⟨$⟩ (pointwiseRespAny⃖ imp (proj₁ al) (proj₁ atl) p∈atl (LPW.map ≈P-reflexive aeql)) 
              where
                open import Data.List.Any.Properties
                module I1 = Inverse ⊥↔Any⊥
                module I2 = Inverse ⊥↔Any⊥

                imp : {l₀ : |L₀|} → {x : |P|} → (p ≈P x) → (x ≈P inj₁ l₀) → const ⊥ l₀
                imp {l₀} {x} p≈x x≈inj₁l₀ = 
                  ⊥-elim $ I2.from ⟨$⟩ (pointwiseRespAny⃖ imp' (proj₁ br) (proj₁ btr) p∈btr (LPW.map ≈P-reflexive beqr))
                  where
                    p≈inj₁l₀ : p ≈P inj₁ l₀
                    p≈inj₁l₀ = ≈P-trans p≈x x≈inj₁l₀

                    imp' : {r₀ : |R₀|} → {z : |P|} → (p ≈P z) → (z ≈P inj₂ r₀) → const ⊥ r₀
                    imp' {r₀} {z} p≈z z≈inj₂r₀ with ≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀
                      where
                        p≈inj₂r₀ : p ≈P inj₂ r₀
                        p≈inj₂r₀ = ≈P-trans p≈z z≈inj₂r₀
                    imp' {r₀} {z} p≈z z≈inj₂r₀ | (₁∼₂ ())
        --]]]
        p← : (p : |P|) → (p ∈P btl) → (p ∈P atl)
        --[[[
        p← p p∈btl = p∈atl
          where
            open import Data.List.Membership.Setoid.Properties
            module E = Equivalence (p∈a⇔p∈b p) 

            p∈b : p ∈P b
            p∈b = ∈-++⁺ˡ ≈P-setoid p∈btl

            p∈a : p ∈P a
            p∈a = E.from ⟨$⟩ p∈b

            p∈atl : p ∈P atl
            p∈atl with ∈-++⁻ ≈P-setoid (proj₁ atl) p∈a
            p∈atl | inj₁ goal = goal
            p∈atl | inj₂ p∈atr = 
              ⊥-elim $ I1.from ⟨$⟩ (pointwiseRespAny⃖ imp (proj₁ bl) (proj₁ btl) p∈btl (LPW.map ≈P-reflexive beql)) 
              where
                open import Data.List.Any.Properties
                module I1 = Inverse ⊥↔Any⊥
                module I2 = Inverse ⊥↔Any⊥

                imp : {l₀ : |L₀|} → {x : |P|} → (p ≈P x) → (x ≈P inj₁ l₀) → const ⊥ l₀
                imp {l₀} {x} p≈x x≈inj₁l₀ = 
                  ⊥-elim $ I2.from ⟨$⟩ (pointwiseRespAny⃖ imp' (proj₁ ar) (proj₁ atr) p∈atr (LPW.map ≈P-reflexive aeqr))
                  where
                    p≈inj₁l₀ : p ≈P inj₁ l₀
                    p≈inj₁l₀ = ≈P-trans p≈x x≈inj₁l₀

                    imp' : {r₀ : |R₀|} → {z : |P|} → (p ≈P z) → (z ≈P inj₂ r₀) → const ⊥ r₀
                    imp' {r₀} {z} p≈z z≈inj₂r₀ with ≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀
                      where
                        p≈inj₂r₀ : p ≈P inj₂ r₀
                        p≈inj₂r₀ = ≈P-trans p≈z z≈inj₂r₀
                    imp' {r₀} {z} p≈z z≈inj₂r₀ | (₁∼₂ ())
        --]]]
        sameElements : (p : |P|) → (p ∈P atl) ⇔ (p ∈P btl)
        sameElements p = equivalence (p→ p) (p← p) 

        module E = Equivalence (c1≈c2⇔sameElementsP atl btl)
    --]]]

    al≈bl : al ≈FL bl
    --[[[
    al≈bl =
      LPW.transitive t'' t' (LPW.symmetric ≈P-sym $ LPW.map ≈P-reflexive beql) 
      where
        t : {l₀' : |L₀|} → {atl₀ : |P|} → {btl₀ : |P|} → (atl₀ ≈P inj₁ l₀') → (atl₀ ≈P btl₀) → (btl₀ ≈P inj₁ l₀')
        t {l₀'} {atl₀} {btl₀} atl₀≈inj₁l₀' atl₀≈btl₀ = ≈P-trans (≈P-sym atl₀≈btl₀) atl₀≈inj₁l₀'

        t' : LPW.Pointwise (λ x → λ y → y ≈P inj₁ x) (proj₁ al) (proj₁ btl)
        t' = LPW.transitive t (LPW.map ≈P-reflexive aeql) atl≈btl

        t'' : {al₀' : |L₀|} → {btl₀ : |P|} → {bl₀' : |L₀|} → (btl₀ ≈P inj₁ al₀') → (inj₁ bl₀' ≈P btl₀) → (al₀' ≈L₀ bl₀')
        t'' {al₀'} {btl₀} {bl₀'} btl₀≈inj₁al₀' inj₁bl₀'≈btl₀ with ≈P-trans (≈P-sym btl₀≈inj₁al₀') (≈P-sym inj₁bl₀'≈btl₀)
        t'' {al₀'} {btl₀} {bl₀'} btl₀≈inj₁al₀' inj₁bl₀'≈btl₀ | ₁∼₁ al₀'≈bl₀' = al₀'≈bl₀' 
    --]]]

    atr≈btr : atr ≈F btr
    --[[[
    atr≈btr with to ⟨$⟩ a≈b  
      where
        open Equivalence (c1≈c2⇔sameElementsP a b)
    atr≈btr | p∈a⇔p∈b =
      E.from ⟨$⟩ sameElements
      where
        p→ : (p : |P|) → (p ∈P atr) → (p ∈P btr)
        --[[[
        p→ p p∈atr = p∈btr 
          where
            open import Data.List.Membership.Setoid.Properties
            module E = Equivalence (p∈a⇔p∈b p) 

            p∈a : p ∈P a
            p∈a = ∈-++⁺ʳ ≈P-setoid (proj₁ atl) p∈atr

            p∈b : p ∈P b
            p∈b = E.to ⟨$⟩ p∈a

            p∈btr : p ∈P btr
            p∈btr with ∈-++⁻ ≈P-setoid (proj₁ btl) p∈b
            p∈btr | inj₁ p∈btl = 
              ⊥-elim $ I1.from ⟨$⟩ (pointwiseRespAny⃖ imp (proj₁ bl) (proj₁ btl) p∈btl (LPW.map ≈P-reflexive beql)) 
              where
                open import Data.List.Any.Properties
                module I1 = Inverse ⊥↔Any⊥
                module I2 = Inverse ⊥↔Any⊥

                imp : {l₀ : |L₀|} → {x : |P|} → (p ≈P x) → (x ≈P inj₁ l₀) → const ⊥ l₀
                imp {l₀} {x} p≈x x≈inj₁l₀ = 
                  ⊥-elim $ I2.from ⟨$⟩ (pointwiseRespAny⃖ imp' (proj₁ ar) (proj₁ atr) p∈atr (LPW.map ≈P-reflexive aeqr))
                  where
                    p≈inj₁l₀ : p ≈P inj₁ l₀
                    p≈inj₁l₀ = ≈P-trans p≈x x≈inj₁l₀

                    imp' : {r₀ : |R₀|} → {z : |P|} → (p ≈P z) → (z ≈P inj₂ r₀) → const ⊥ r₀
                    imp' {r₀} {z} p≈z z≈inj₂r₀ with ≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀
                      where
                        p≈inj₂r₀ : p ≈P inj₂ r₀
                        p≈inj₂r₀ = ≈P-trans p≈z z≈inj₂r₀
                    imp' {r₀} {z} p≈z z≈inj₂r₀ | (₁∼₂ ())
            p∈btr | inj₂ goal = goal

        --]]]
        p← : (p : |P|) → (p ∈P btr) → (p ∈P atr)
        --[[[
        p← p p∈btr = p∈atr
          where
            open import Data.List.Membership.Setoid.Properties
            module E = Equivalence (p∈a⇔p∈b p) 

            p∈b : p ∈P b
            p∈b = ∈-++⁺ʳ ≈P-setoid (proj₁ btl) p∈btr

            p∈a : p ∈P a
            p∈a = E.from ⟨$⟩ p∈b

            p∈atr : p ∈P atr
            p∈atr with ∈-++⁻ ≈P-setoid (proj₁ atl) p∈a
            p∈atr | inj₁ p∈atl = 
              ⊥-elim $ I1.from ⟨$⟩ (pointwiseRespAny⃖ imp (proj₁ al) (proj₁ atl) p∈atl (LPW.map ≈P-reflexive aeql)) 
              where
                open import Data.List.Any.Properties
                module I1 = Inverse ⊥↔Any⊥
                module I2 = Inverse ⊥↔Any⊥

                imp : {l₀ : |L₀|} → {x : |P|} → (p ≈P x) → (x ≈P inj₁ l₀) → const ⊥ l₀
                imp {l₀} {x} p≈x x≈inj₁l₀ = 
                  ⊥-elim $ I2.from ⟨$⟩ (pointwiseRespAny⃖ imp' (proj₁ br) (proj₁ btr) p∈btr (LPW.map ≈P-reflexive beqr))
                  where
                    p≈inj₁l₀ : p ≈P inj₁ l₀
                    p≈inj₁l₀ = ≈P-trans p≈x x≈inj₁l₀

                    imp' : {r₀ : |R₀|} → {z : |P|} → (p ≈P z) → (z ≈P inj₂ r₀) → const ⊥ r₀
                    imp' {r₀} {z} p≈z z≈inj₂r₀ with ≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀
                      where
                        p≈inj₂r₀ : p ≈P inj₂ r₀
                        p≈inj₂r₀ = ≈P-trans p≈z z≈inj₂r₀
                    imp' {r₀} {z} p≈z z≈inj₂r₀ | (₁∼₂ ())
            p∈atr | inj₂ goal = goal

        --]]]
        sameElements : (p : |P|) → (p ∈P atr) ⇔ (p ∈P btr)
        sameElements p = equivalence (p→ p) (p← p) 

        module E = Equivalence (c1≈c2⇔sameElementsP atr btr)
    --]]]

    ar≈br : ar ≈FR br
    --[[[
    ar≈br =
      LPW.transitive t'' t' (LPW.symmetric ≈P-sym $ LPW.map ≈P-reflexive beqr) 
      where
        t : {r₀' : |R₀|} → {atr₀ : |P|} → {btr₀ : |P|} → (atr₀ ≈P inj₂ r₀') → (atr₀ ≈P btr₀) → (btr₀ ≈P inj₂ r₀')
        t {r₀'} {atr₀} {btr₀} atr₀≈inj₁r₀' atr₀≈btr₀ = ≈P-trans (≈P-sym atr₀≈btr₀) atr₀≈inj₁r₀'

        t' : LPW.Pointwise (λ x → λ y → y ≈P inj₂ x) (proj₁ ar) (proj₁ btr)
        t' = LPW.transitive t (LPW.map ≈P-reflexive aeqr) atr≈btr

        t'' : {ar₀' : |R₀|} → {btr₀ : |P|} → {br₀' : |R₀|} → (btr₀ ≈P inj₂ ar₀') → (inj₂ br₀' ≈P btr₀) → (ar₀' ≈R₀ br₀')
        t'' {ar₀'} {btr₀} {br₀'} btr₀≈inj₁ar₀' inj₁br₀'≈btr₀ with ≈P-trans (≈P-sym btr₀≈inj₁ar₀') (≈P-sym inj₁br₀'≈btr₀)
        t'' {ar₀'} {btr₀} {br₀'} btr₀≈inj₁ar₀' inj₁br₀'≈btr₀ | ₂∼₂ ar₀'≈br₀' = ar₀'≈br₀' 
    --]]]

--]]]

|g|-⊥ : |g| ⊥F ≈' ⊥'
--[[[
|g|-⊥ with decompose ⊥F 
|g|-⊥ | l , r , (hl ∷ tl , _) , ([] , _) , aeql , aeqr , ()
|g|-⊥ | l , r , ([] , _) , (hr ∷ tr , _) , aeql , aeqr , ()
|g|-⊥ | l , r , (hl ∷ tl , _) , (hr ∷ tr , _) , aeql , aeqr , ()
|g|-⊥ | ([] , []-FreeL) , ([] , []-FreeR) , ([] , []-Free) , ([] , []-Free) , [] , [] , aconcat =
  |gL|-⊥ , |gR|-⊥
--]]]

|g|-∨ : (a b : Carrier-FP) → (|g| $ a ∨F b) ≈' ((|g| a) ∨' (|g| b))
--[[[
|g|-∨ a b with decompose a | decompose b | decompose (a ∨F b)
|g|-∨ a b | al , ar , atl , atr , aeql , aeqr , aconcat@PE.refl
           | bl , br , btl , btr , beql , beqr , bconcat@PE.refl
           | jl , jr , jtl , jtr , jeql , jeqr , jconcat =
  ≈L-trans (|gL|-≈ jl (al ∨FL bl) jl≈al∨bl) (|gL|-∨ al bl) , ≈R-trans (|gR|-≈ jr (ar ∨FR br) jr≈ar∨br) (|gR|-∨ ar br)
  where
   jtl≈atl∨btl : jtl ≈F (atl ∨F btl)
   --[[[
   jtl≈atl∨btl = E-jtl≈atl.from ⟨$⟩ sameElements
     where
       module E-jtl≈atl = Equivalence (c1≈c2⇔sameElementsP jtl (atl ∨F btl))

       p→ : (p : |P|) → (p ∈P jtl) → (p ∈P (atl ∨F btl))
       --[[[
       p→ p p∈jtl = anyEliminate (proj₁ jl) elim z
         where
           open import Data.List.Membership.Setoid.Properties

           imp : {l₀ : |L₀|} → {x : |P|} → (p ≈P x) → (x ≈P inj₁ l₀) → (p ≈P inj₁ l₀)
           imp {l₀} {x} p≈x x≈inj₁l₀ = ≈P-trans p≈x x≈inj₁l₀

           jeql' : LPW.Pointwise (λ x y → y ≈P inj₁ x) (proj₁ jl) (proj₁ jtl)
           jeql' = LPW.reflexive ≈P-reflexive jeql

           z : Any (λ l₀ → p ≈P inj₁ l₀) (proj₁ jl)
           z = pointwiseRespAny⃖ imp (proj₁ jl) (proj₁ jtl) p∈jtl jeql'

           p∈jtl++jtr : p ∈P' (proj₁ jtl) ++ (proj₁ jtr)
           p∈jtl++jtr = ∈-++⁺ˡ ≈P-setoid p∈jtl

           p∈a∨b : p ∈P (a ∨F b)
           p∈a∨b = PE.subst (λ x → p ∈P' x) (PE.sym jconcat) p∈jtl++jtr

           -- we need to apply jconcat to p∈jtl+jtr... but this is a bit complicated
           --p∈a∨b : p ∈ (proj₁ atl ++ proj₁ btl)

           --this eliminates z
           elim : AnyEliminator {ℓQ = l0} |L₀| (p ∈P (atl ∨F btl)) (λ l₀ → p ≈P inj₁ l₀) (proj₁ jl)
           elim l₀ f p≈inj₁l₀ l₀∈jl with E.to ⟨$⟩ p∈a∨b   
             where
               module E = Equivalence (x∈∨⇔P∨-P a b (a ∨F b) (≈F-refl {a ∨F b}) p)
           elim l₀ f p≈inj₁l₀ l₀∈jl | inj₁ (p∈a , ¬p⊑b) with p∈atl⊎p∈atr
             where
               p∈atl++atr : p ∈P' (proj₁ atl) ++ (proj₁ atr)
               p∈atl++atr = PE.subst (λ x → p ∈P' x) aconcat p∈a

               p∈atl⊎p∈atr : (p ∈P atl) ⊎ (p ∈P atr)
               p∈atl⊎p∈atr = ∈-++⁻ ≈P-setoid (proj₁ atl) p∈atl++atr
           elim l₀ f p≈inj₁l₀ l₀∈jl | inj₁ (p∈a , ¬p⊑b) | inj₁ p∈atl =
             from ⟨$⟩ inj₁ (p∈atl , ¬p⊑btl)
             where
               open Equivalence (x∈∨⇔P∨-P atl btl (atl ∨F btl) (≈F-refl {atl ∨F btl}) p)

               ¬p⊑btl : ¬ Any (p ⊑P_) (proj₁ btl)
               ¬p⊑btl p⊑btl = ¬p⊑b (++⁺ˡ p⊑btl)
                 where
                   open import Data.List.Any.Properties           
           elim l₀ f p≈inj₁l₀ l₀∈jl | inj₁ (p∈a , ¬p⊑b) | inj₂ p∈atr = 
             ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ ar) (proj₁ atr) p∈atr (LPW.map ≈P-reflexive aeqr) 
             where
               open import Data.List.Any.Properties
               module I = Inverse (⊥↔Any⊥ {xs = proj₁ ar})

               imp' : {r₀ : |R₀|} → {p' : |P|} → (p ≈P p') → (p' ≈P inj₂ r₀) → const ⊥ r₀
               imp' {r₀} {p'} p≈p' p'≈inj₂r₀ with (≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀) 
                 where
                   p≈inj₂r₀ : p ≈P (inj₂ r₀)
                   p≈inj₂r₀ = ≈P-trans p≈p' p'≈inj₂r₀
               imp' {r₀} {p'} p≈p' p'≈inj₂r₀ | (₁∼₂ ())
           elim l₀ f p≈inj₁l₀ l₀∈jl | inj₂ (inj₁ (p∈b , ¬p⊑a)) with p∈btl⊎p∈btr
             where
               p∈btl++btr : p ∈P' (proj₁ btl) ++ (proj₁ btr)
               p∈btl++btr = PE.subst (λ x → p ∈P' x) bconcat p∈b

               p∈btl⊎p∈btr : (p ∈P btl) ⊎ (p ∈P btr)
               p∈btl⊎p∈btr = ∈-++⁻ ≈P-setoid (proj₁ btl) p∈btl++btr
           elim l₀ f p≈inj₁l₀ l₀∈jl | inj₂ (inj₁ (p∈b , ¬p⊑a)) | inj₁ p∈btl =
             from ⟨$⟩ inj₂ (inj₁ (p∈btl , ¬p⊑atl))
             where
               open Equivalence (x∈∨⇔P∨-P atl btl (atl ∨F btl) (≈F-refl {atl ∨F btl}) p)

               ¬p⊑atl : ¬ Any (p ⊑P_) (proj₁ atl)
               ¬p⊑atl p⊑atl = ¬p⊑a (++⁺ˡ p⊑atl)
                 where
                   open import Data.List.Any.Properties      
           elim l₀ f p≈inj₁l₀ l₀∈jl | inj₂ (inj₁ (p∈b , ¬p⊑a)) | inj₂ p∈btr =
             ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ br) (proj₁ btr) p∈btr (LPW.map ≈P-reflexive beqr) 
             where
               open import Data.List.Any.Properties
               module I = Inverse (⊥↔Any⊥ {xs = proj₁ br})

               imp' : {r₀ : |R₀|} → {p' : |P|} → (p ≈P p') → (p' ≈P inj₂ r₀) → const ⊥ r₀
               imp' {r₀} {p'} p≈p' p'≈inj₂r₀ with (≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀) 
                 where
                   p≈inj₂r₀ : p ≈P (inj₂ r₀)
                   p≈inj₂r₀ = ≈P-trans p≈p' p'≈inj₂r₀
               imp' {r₀} {p'} p≈p' p'≈inj₂r₀ | (₁∼₂ ())                 
           elim l₀ f p≈inj₁l₀ l₀∈jl | inj₂ (inj₂ (p∈a , p∈b)) with p∈atl⊎p∈atr | p∈btl⊎p∈btr
             where
               p∈atl++atr : p ∈P' (proj₁ atl) ++ (proj₁ atr)
               p∈atl++atr = PE.subst (λ x → p ∈P' x) aconcat p∈a

               p∈atl⊎p∈atr : (p ∈P atl) ⊎ (p ∈P atr)
               p∈atl⊎p∈atr = ∈-++⁻ ≈P-setoid (proj₁ atl) p∈atl++atr

               p∈btl++btr : p ∈P' (proj₁ btl) ++ (proj₁ btr)
               p∈btl++btr = PE.subst (λ x → p ∈P' x) bconcat p∈b

               p∈btl⊎p∈btr : (p ∈P btl) ⊎ (p ∈P btr)
               p∈btl⊎p∈btr = ∈-++⁻ ≈P-setoid (proj₁ btl) p∈btl++btr
           elim l₀ f p≈inj₁l₀ l₀∈jl | inj₂ (inj₂ (p∈a , p∈b)) | inj₁ p∈atl | inj₁ p∈btl =
             from ⟨$⟩ inj₂ (inj₂ (p∈atl , p∈btl))
             where
               open Equivalence (x∈∨⇔P∨-P atl btl (atl ∨F btl) (≈F-refl {atl ∨F btl}) p)
           elim l₀ f p≈inj₁l₀ l₀∈jl | inj₂ (inj₂ (p∈a , p∈b)) | inj₂ p∈atr | _ =
             ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ ar) (proj₁ atr) p∈atr (LPW.map ≈P-reflexive aeqr) 
             where
               open import Data.List.Any.Properties
               module I = Inverse (⊥↔Any⊥ {xs = proj₁ ar})

               imp' : {r₀ : |R₀|} → {p' : |P|} → (p ≈P p') → (p' ≈P inj₂ r₀) → const ⊥ r₀
               imp' {r₀} {p'} p≈p' p'≈inj₂r₀ with (≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀) 
                 where
                   p≈inj₂r₀ : p ≈P (inj₂ r₀)
                   p≈inj₂r₀ = ≈P-trans p≈p' p'≈inj₂r₀
               imp' {r₀} {p'} p≈p' p'≈inj₂r₀ | (₁∼₂ ())
           elim l₀ f p≈inj₁l₀ l₀∈jl | inj₂ (inj₂ (p∈a , p∈b)) | _ | inj₂ p∈btr =
             ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ br) (proj₁ btr) p∈btr (LPW.map ≈P-reflexive beqr) 
             where
               open import Data.List.Any.Properties
               module I = Inverse (⊥↔Any⊥ {xs = proj₁ br})

               imp' : {r₀ : |R₀|} → {p' : |P|} → (p ≈P p') → (p' ≈P inj₂ r₀) → const ⊥ r₀
               imp' {r₀} {p'} p≈p' p'≈inj₂r₀ with (≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀) 
                 where
                   p≈inj₂r₀ : p ≈P (inj₂ r₀)
                   p≈inj₂r₀ = ≈P-trans p≈p' p'≈inj₂r₀
               imp' {r₀} {p'} p≈p' p'≈inj₂r₀ | (₁∼₂ ())       
           --]]]

       p← : (p : |P|) → (p ∈P (atl ∨F btl)) → (p ∈P jtl) 
       --[[[
       p← p p∈atl∨btl with to ⟨$⟩ p∈atl∨btl 
         where
           open Equivalence (x∈∨⇔P∨-P atl btl (atl ∨F btl) (≈F-refl {atl ∨F btl}) p)
       p← p p∈atl∨btl | inj₁ (p∈atl , ¬p⊑btl) = 
         anyEliminate (proj₁ al) elim p≈inj₁al
         where
           imp : {l₀ : |L₀|} → {p' : |P|} → p ≈P p' → p' ≈P (inj₁ l₀) → p ≈P inj₁ l₀
           imp {l₀} {p'} p≈p' p'≈inj₁l₀ = ≈P-trans p≈p' p'≈inj₁l₀

           p≈inj₁al : Any (λ · → p ≈P inj₁ ·) (proj₁ al)
           p≈inj₁al = pointwiseRespAny⃖ imp (proj₁ al) (proj₁ atl) p∈atl (LPW.map ≈P-reflexive aeql)

           elim : AnyEliminator {ℓQ = l0} |L₀| (p ∈P jtl) (λ · → p ≈P inj₁ ·) (proj₁ al)
           elim l₀ f p≈inj₁l₀ l₀∈al = p∈jtl
             where
               open import Data.List.Any.Properties

               p∈a : p ∈P a
               p∈a = ++⁺ˡ p∈atl

               ¬p⊑btr : ¬ Any (p ⊑P_) (proj₁ btr)
               --[[[
               ¬p⊑btr p⊑btr =
                 ⊥-elim $ from ⟨$⟩ (pointwiseRespAny⃖ imp' (proj₁ br) (proj₁ btr) p⊑btr (LPW.map ≈P-reflexive beqr)) 
                 where
                   open Inverse (⊥↔Any⊥ {xs = proj₁ br})

                   imp' : {r₀ : |R₀|} → {p' : |P|} → p ⊑P p' → p' ≈P inj₂ r₀ → const ⊥ r₀
                   imp' {r₀} {p'} p⊑p' p'≈inj₂r₀ with inj₁l₀⊑inj₂r₀ -- with (≈P-trans (≈P-sym p≈inj₁l₀ )
                     where
                       open import Relation.Binary.PartialOrderReasoning (DecPoset.poset ⊑P-decPoset)

                       inj₁l₀⊑inj₂r₀ : inj₁ l₀ ⊑P inj₂ r₀
                       inj₁l₀⊑inj₂r₀ = begin
                         (inj₁ l₀) ≈⟨ ≈P-sym p≈inj₁l₀ ⟩
                         p ≤⟨ p⊑p' ⟩
                         p' ≈⟨ p'≈inj₂r₀ ⟩
                         (inj₂ r₀)
                        ∎
                   imp' {r₀} {p'} p⊑p' p'≈inj₂r₀ | ₁∼₂ ()
               --]]]

               ¬p⊑b : ¬ Any (p ⊑P_) ((proj₁ btl) ++ (proj₁ btr))
               ¬p⊑b p⊑btl++btr with ++⁻ (proj₁ btl) p⊑btl++btr
               ¬p⊑b p⊑btl++btr | inj₁ p⊑btl = ¬p⊑btl p⊑btl
               ¬p⊑b p⊑btl++btr | inj₂ p⊑btr = ¬p⊑btr p⊑btr

               open Equivalence (x∈∨⇔P∨-P a b (a ∨F b) (≈F-refl {a ∨F b}) p)

               p∈a∨b : p ∈P (a ∨F b)
               p∈a∨b = from ⟨$⟩ inj₁ (p∈a , ¬p⊑b)  

               p∈jtl++jtr : p ∈P' (proj₁ jtl ++ proj₁ jtr)
               p∈jtl++jtr = PE.subst (λ · → p ∈P' ·) jconcat p∈a∨b

               p∈jtl : p ∈P' (proj₁ jtl)
               --[[[
               p∈jtl with ++⁻ (proj₁ jtl) p∈jtl++jtr
               p∈jtl | inj₁ goal = goal
               p∈jtl | inj₂ p∈jtr = 
                 ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ jr) (proj₁ jtr) p∈jtr (LPW.map ≈P-reflexive jeqr) 
                 where
                   module I = Inverse (⊥↔Any⊥ {xs = proj₁ jr})

                   imp' : {r₀ : |R₀|} → {p' : |P|} → p ≈P p' → p' ≈P inj₂ r₀ → const ⊥ r₀
                   imp' {r₀} {p'} p≈p' p'≈inj₂r₀ with inj₁l₀≈inj₂r₀ 
                     where
                       open import Relation.Binary.EqReasoning (≈P-setoid)

                       inj₁l₀≈inj₂r₀ : (inj₁ l₀) ≈P (inj₂ r₀)
                       inj₁l₀≈inj₂r₀ = 
                         begin
                           inj₁ l₀ ≈⟨ ≈P-sym p≈inj₁l₀ ⟩
                           p ≈⟨ p≈p' ⟩
                           p' ≈⟨ p'≈inj₂r₀ ⟩
                           inj₂ r₀
                          ∎ 
                   imp' {r₀} {p'} p≈p' p'≈inj₂r₀ | ₁∼₂ ()
               --]]]
       p← p p∈atl∨btl | inj₂ (inj₁ (p∈btl , ¬p⊑atl)) = 
         anyEliminate (proj₁ bl) elim p≈inj₁bl
         where
           imp : {l₀ : |L₀|} → {p' : |P|} → p ≈P p' → p' ≈P (inj₁ l₀) → p ≈P inj₁ l₀
           imp {l₀} {p'} p≈p' p'≈inj₁l₀ = ≈P-trans p≈p' p'≈inj₁l₀

           p≈inj₁bl : Any (λ · → p ≈P inj₁ ·) (proj₁ bl)
           p≈inj₁bl = pointwiseRespAny⃖ imp (proj₁ bl) (proj₁ btl) p∈btl (LPW.map ≈P-reflexive beql)

           elim : AnyEliminator {ℓQ = l0} |L₀| (p ∈P jtl) (λ · → p ≈P inj₁ ·) (proj₁ bl)
           elim l₀ f p≈inj₁l₀ l₀∈bl = p∈jtl
             where
               open import Data.List.Any.Properties

               p∈b : p ∈P b
               p∈b = ++⁺ˡ p∈btl

               ¬p⊑atr : ¬ Any (p ⊑P_) (proj₁ atr)
               --[[[
               ¬p⊑atr p⊑atr =
                 ⊥-elim $ from ⟨$⟩ (pointwiseRespAny⃖ imp' (proj₁ ar) (proj₁ atr) p⊑atr (LPW.map ≈P-reflexive aeqr)) 
                 where
                   open Inverse (⊥↔Any⊥ {xs = proj₁ ar})

                   imp' : {r₀ : |R₀|} → {p' : |P|} → p ⊑P p' → p' ≈P inj₂ r₀ → const ⊥ r₀
                   imp' {r₀} {p'} p⊑p' p'≈inj₂r₀ with inj₁l₀⊑inj₂r₀
                     where
                       open import Relation.Binary.PartialOrderReasoning (DecPoset.poset ⊑P-decPoset)

                       inj₁l₀⊑inj₂r₀ : inj₁ l₀ ⊑P inj₂ r₀
                       inj₁l₀⊑inj₂r₀ = begin
                         (inj₁ l₀) ≈⟨ ≈P-sym p≈inj₁l₀ ⟩
                         p ≤⟨ p⊑p' ⟩
                         p' ≈⟨ p'≈inj₂r₀ ⟩
                         (inj₂ r₀)
                        ∎
                   imp' {r₀} {p'} p⊑p' p'≈inj₂r₀ | ₁∼₂ ()
               --]]]

               ¬p⊑a : ¬ Any (p ⊑P_) ((proj₁ atl) ++ (proj₁ atr))
               ¬p⊑a p⊑atl++atr with ++⁻ (proj₁ atl) p⊑atl++atr
               ¬p⊑a p⊑atl++atr | inj₁ p⊑atl = ¬p⊑atl p⊑atl
               ¬p⊑a p⊑atl++atr | inj₂ p⊑atr = ¬p⊑atr p⊑atr

               open Equivalence (x∈∨⇔P∨-P a b (a ∨F b) (≈F-refl {a ∨F b}) p)

               p∈a∨b : p ∈P (a ∨F b)
               p∈a∨b = from ⟨$⟩ inj₂ (inj₁ (p∈b , ¬p⊑a))

               p∈jtl++jtr : p ∈P' (proj₁ jtl ++ proj₁ jtr)
               p∈jtl++jtr = PE.subst (λ · → p ∈P' ·) jconcat p∈a∨b

               p∈jtl : p ∈P' (proj₁ jtl)
               --[[[
               p∈jtl with ++⁻ (proj₁ jtl) p∈jtl++jtr
               p∈jtl | inj₁ goal = goal
               p∈jtl | inj₂ p∈jtr = 
                 ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ jr) (proj₁ jtr) p∈jtr (LPW.map ≈P-reflexive jeqr) 
                 where
                   module I = Inverse (⊥↔Any⊥ {xs = proj₁ jr})

                   imp' : {r₀ : |R₀|} → {p' : |P|} → p ≈P p' → p' ≈P inj₂ r₀ → const ⊥ r₀
                   imp' {r₀} {p'} p≈p' p'≈inj₂r₀ with inj₁l₀≈inj₂r₀ 
                     where
                       open import Relation.Binary.EqReasoning (≈P-setoid)

                       inj₁l₀≈inj₂r₀ : (inj₁ l₀) ≈P (inj₂ r₀)
                       inj₁l₀≈inj₂r₀ = 
                         begin
                           inj₁ l₀ ≈⟨ ≈P-sym p≈inj₁l₀ ⟩
                           p ≈⟨ p≈p' ⟩
                           p' ≈⟨ p'≈inj₂r₀ ⟩
                           inj₂ r₀
                          ∎ 
                   imp' {r₀} {p'} p≈p' p'≈inj₂r₀ | ₁∼₂ ()
               --]]]
       p← p p∈atl∨btl | inj₂ (inj₂ (p∈atl , p∈btl)) = 
         anyEliminate (proj₁ bl) elim p≈inj₁bl
         where
           open Equivalence (x∈∨⇔P∨-P a b (a ∨F b) (≈F-refl {a ∨F b}) p)
           open import Data.List.Any.Properties

           imp : {l₀ : |L₀|} → {p' : |P|} → p ≈P p' → p' ≈P (inj₁ l₀) → p ≈P inj₁ l₀
           imp {l₀} {p'} p≈p' p'≈inj₁l₀ = ≈P-trans p≈p' p'≈inj₁l₀

           p≈inj₁bl : Any (λ · → p ≈P inj₁ ·) (proj₁ bl)
           p≈inj₁bl = pointwiseRespAny⃖ imp (proj₁ bl) (proj₁ btl) p∈btl (LPW.map ≈P-reflexive beql)

           elim : AnyEliminator {ℓQ = l0} |L₀| (p ∈P jtl) (λ · → p ≈P inj₁ ·) (proj₁ bl)
           --[[[
           elim l₀ f p≈inj₁l₀ l₀∈bl = p∈jtl
             where
               p∈a : p ∈P a
               p∈a = ++⁺ˡ p∈atl

               p∈b : p ∈P b
               p∈b = ++⁺ˡ p∈btl

               p∈a∨b : p ∈P (a ∨F b)
               p∈a∨b = from ⟨$⟩ inj₂ (inj₂ (p∈a , p∈b))

               p∈jtl++jtr : p ∈P' (proj₁ jtl ++ proj₁ jtr)
               p∈jtl++jtr = PE.subst (λ · → p ∈P' ·) jconcat p∈a∨b

               p∈jtl : p ∈P' (proj₁ jtl)
               --[[[
               p∈jtl with ++⁻ (proj₁ jtl) p∈jtl++jtr
               p∈jtl | inj₁ goal = goal
               p∈jtl | inj₂ p∈jtr = 
                 ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ jr) (proj₁ jtr) p∈jtr (LPW.map ≈P-reflexive jeqr) 
                 where
                   module I = Inverse (⊥↔Any⊥ {xs = proj₁ jr})

                   imp' : {r₀ : |R₀|} → {p' : |P|} → p ≈P p' → p' ≈P inj₂ r₀ → const ⊥ r₀
                   imp' {r₀} {p'} p≈p' p'≈inj₂r₀ with inj₁l₀≈inj₂r₀ 
                     where
                       open import Relation.Binary.EqReasoning (≈P-setoid)

                       inj₁l₀≈inj₂r₀ : (inj₁ l₀) ≈P (inj₂ r₀)
                       inj₁l₀≈inj₂r₀ = 
                         begin
                           inj₁ l₀ ≈⟨ ≈P-sym p≈inj₁l₀ ⟩
                           p ≈⟨ p≈p' ⟩
                           p' ≈⟨ p'≈inj₂r₀ ⟩
                           inj₂ r₀
                          ∎ 
                   imp' {r₀} {p'} p≈p' p'≈inj₂r₀ | ₁∼₂ ()
               --]]]
       --]]]
       --]]]

       sameElements : (p : |P|) → (p ∈P jtl) ⇔ (p ∈P (atl ∨F btl))
       sameElements p = equivalence (p→ p) (p← p)
   --]]]

   jl≈al∨bl : jl ≈FL (al ∨FL bl)
   --[[[
   jl≈al∨bl = E.from ⟨$⟩ sameElements 
     where
       module E = Equivalence (c1≈c2⇔sameElementsL jl (al ∨FL bl))

       l₀→ : (l₀ : |L₀|) → (l₀ ∈L jl) → (l₀ ∈L (al ∨FL bl))
       --[[[
       l₀→ l₀ l₀∈jl with to ⟨$⟩ inj₁l₀∈atl∨btl  
         where
           open Equivalence (x∈∨⇔P∨-P atl btl (atl ∨F btl) (≈F-refl {atl ∨F btl}) (inj₁ l₀))

           inj₁l₀∈jtl : (inj₁ l₀) ∈P jtl
           inj₁l₀∈jtl = pointwiseRespAny imp (proj₁ jl) (proj₁ jtl) l₀∈jl (LPW.reflexive ≈P-reflexive jeql)
             where
               imp : {l₀' : |L₀|} → {p : |P|} → l₀ ≈L₀ l₀' → p ≈P inj₁ l₀' → (inj₁ l₀ ≈P p)
               imp {l₀'} {p} l₀≈l₀' p≈inj₁l₀' = ≈P-sym (≈P-trans p≈inj₁l₀' (₁∼₁ $ ≈L₀-sym l₀≈l₀'))

           inj₁l₀∈atl∨btl : (inj₁ l₀) ∈P (atl ∨F btl)
           inj₁l₀∈atl∨btl = p∈c1≈c2-P {inj₁ l₀} {jtl} {atl ∨F btl} jtl≈atl∨btl inj₁l₀∈jtl

       l₀→ l₀ l₀∈jl | inj₁ (inj₁l₀∈atl , ¬inj₁l₀⊑btl) = 
         from ⟨$⟩ inj₁ (l₀∈al , ¬l₀⊑bl)
         where
           open Equivalence (x∈∨⇔P∨-L al bl (al ∨FL bl) (≈FL-refl {al ∨FL bl}) l₀)

           l₀∈al : l₀ ∈L al
           l₀∈al = pointwiseRespAny⃖ imp (proj₁ al) (proj₁ atl) inj₁l₀∈atl (LPW.map ≈P-reflexive aeql)
             where
               imp : {l₀' : |L₀|} → {p : |P|} → inj₁ l₀ ≈P p → p ≈P inj₁ l₀' → l₀ ≈L₀ l₀'
               imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' with ≈P-trans inj₁l₀≈p p≈inj₁l₀'
               imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' | ₁∼₁ l₀≈l₀' = l₀≈l₀'

           ¬l₀⊑bl : ¬ Any (l₀ ⊑L₀_) (proj₁ bl)
           ¬l₀⊑bl l₀⊑bl = ¬inj₁l₀⊑btl inj₁l₀⊑btl
             where
               inj₁l₀⊑btl : Any (inj₁ l₀ ⊑P_) (proj₁ btl)
               inj₁l₀⊑btl = pointwiseRespAny imp (proj₁ bl) (proj₁ btl) l₀⊑bl (LPW.map ≈P-reflexive beql)
                 where
                   imp : {l₀' : |L₀|} → {p : |P|} → l₀ ⊑L₀ l₀' → p ≈P inj₁ l₀' → inj₁ l₀ ⊑P p
                   imp {l₀'} {p} l₀⊑l₀' p≈inj₁l₀' = ⊑P-trans (₁∼₁ l₀⊑l₀') (⊑P-reflexive (≈P-sym p≈inj₁l₀'))

       l₀→ l₀ l₀∈jl | inj₂ (inj₁ (inj₁l₀∈btl , ¬inj₁l₀⊑atl)) =
         from ⟨$⟩ inj₂ (inj₁ (l₀∈bl , ¬l₀⊑al))
         where
           open Equivalence (x∈∨⇔P∨-L al bl (al ∨FL bl) (≈FL-refl {al ∨FL bl}) l₀)

           l₀∈bl : l₀ ∈L bl
           l₀∈bl = pointwiseRespAny⃖ imp (proj₁ bl) (proj₁ btl) inj₁l₀∈btl (LPW.map ≈P-reflexive beql)
             where
               imp : {l₀' : |L₀|} → {p : |P|} → inj₁ l₀ ≈P p → p ≈P inj₁ l₀' → l₀ ≈L₀ l₀'
               imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' with ≈P-trans inj₁l₀≈p p≈inj₁l₀'
               imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' | ₁∼₁ l₀≈l₀' = l₀≈l₀'

           ¬l₀⊑al : ¬ Any (l₀ ⊑L₀_) (proj₁ al)
           ¬l₀⊑al l₀⊑al = ¬inj₁l₀⊑atl inj₁l₀⊑atl
             where
               inj₁l₀⊑atl : Any (inj₁ l₀ ⊑P_) (proj₁ atl)
               inj₁l₀⊑atl = pointwiseRespAny imp (proj₁ al) (proj₁ atl) l₀⊑al (LPW.map ≈P-reflexive aeql)
                 where
                   imp : {l₀' : |L₀|} → {p : |P|} → l₀ ⊑L₀ l₀' → p ≈P inj₁ l₀' → inj₁ l₀ ⊑P p
                   imp {l₀'} {p} l₀⊑l₀' p≈inj₁l₀' = ⊑P-trans (₁∼₁ l₀⊑l₀') (⊑P-reflexive (≈P-sym p≈inj₁l₀'))

       l₀→ l₀ l₀∈jl | inj₂ (inj₂ (inj₁l₀∈atl , inj₁l₀∈btl)) =
         from ⟨$⟩ inj₂ (inj₂ (l₀∈al , l₀∈bl))
         where
           open Equivalence (x∈∨⇔P∨-L al bl (al ∨FL bl) (≈FL-refl {al ∨FL bl}) l₀)

           l₀∈al : l₀ ∈L al
           l₀∈al = pointwiseRespAny⃖ imp (proj₁ al) (proj₁ atl) inj₁l₀∈atl (LPW.map ≈P-reflexive aeql)
             where
               imp : {l₀' : |L₀|} → {p : |P|} → inj₁ l₀ ≈P p → p ≈P inj₁ l₀' → l₀ ≈L₀ l₀'
               imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' with ≈P-trans inj₁l₀≈p p≈inj₁l₀'
               imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' | ₁∼₁ l₀≈l₀' = l₀≈l₀'

           l₀∈bl : l₀ ∈L bl
           l₀∈bl = pointwiseRespAny⃖ imp (proj₁ bl) (proj₁ btl) inj₁l₀∈btl (LPW.map ≈P-reflexive beql)
             where
               imp : {l₀' : |L₀|} → {p : |P|} → inj₁ l₀ ≈P p → p ≈P inj₁ l₀' → l₀ ≈L₀ l₀'
               imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' with ≈P-trans inj₁l₀≈p p≈inj₁l₀'
               imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' | ₁∼₁ l₀≈l₀' = l₀≈l₀'
       --]]]    


       l₀← : (l₀ : |L₀|) → (l₀ ∈L (al ∨FL bl)) → (l₀ ∈L jl)
       --[[[
       l₀← l₀ l₀∈al∨bl = l₀∈jl
         where
           inj₁l₀∈atl∨btl : (inj₁ l₀) ∈P (atl ∨F btl)
           inj₁l₀∈atl∨btl with to ⟨$⟩ l₀∈al∨bl
             where
               open Equivalence (x∈∨⇔P∨-L al bl (al ∨FL bl) (≈FL-refl {al ∨FL bl}) l₀)
           inj₁l₀∈atl∨btl | inj₁ (l₀∈al , ¬l₀⊑bl) = from ⟨$⟩ inj₁ (inj₁l₀∈atl , ¬inj₁l₀⊑btl)
             where
               open Equivalence (x∈∨⇔P∨-P atl btl (atl ∨F btl) (≈F-refl {atl ∨F btl}) (inj₁ l₀))

               inj₁l₀∈atl : (inj₁ l₀) ∈P atl
               inj₁l₀∈atl = pointwiseRespAny imp (proj₁ al) (proj₁ atl) l₀∈al (LPW.map ≈P-reflexive aeql)
                 where 
                   imp : {l₀' : |L₀|} → {p : |P|} → l₀ ≈L₀ l₀' → p ≈P (inj₁ l₀') → inj₁ l₀ ≈P p
                   imp {l₀'} {p} l₀≈l₀' p≈inj₁l₀' = ≈P-trans (₁∼₁ l₀≈l₀') (≈P-sym p≈inj₁l₀') 

               ¬inj₁l₀⊑btl : ¬ Any (inj₁ l₀ ⊑P_) (proj₁ btl)
               ¬inj₁l₀⊑btl inj₁l₀⊑btl = ¬l₀⊑bl l₀⊑bl
                 where
                   imp : {l₀' : |L₀|} → {p : |P|} → inj₁ l₀ ⊑P p → p ≈P inj₁ l₀' → l₀ ⊑L₀ l₀' 
                   imp {l₀'} {p} inj₁l₀⊑p p≈inj₁l₀' with ⊑P-trans inj₁l₀⊑p (⊑P-reflexive p≈inj₁l₀')
                   imp {l₀'} {p} inj₁l₀⊑p p≈inj₁l₀' | ₁∼₁ l₀⊑l₀' = l₀⊑l₀'

                   l₀⊑bl : Any (l₀ ⊑L₀_) (proj₁ bl)
                   l₀⊑bl = pointwiseRespAny⃖ imp (proj₁ bl) (proj₁ btl) inj₁l₀⊑btl (LPW.map ≈P-reflexive beql)
           inj₁l₀∈atl∨btl | inj₂ (inj₁ (l₀∈bl , ¬l₀⊑al)) = from ⟨$⟩ (inj₂ $ inj₁ (inj₁l₀∈btl , ¬inj₁l₀⊑atl)) 
             where
               open Equivalence (x∈∨⇔P∨-P atl btl (atl ∨F btl) (≈F-refl {atl ∨F btl}) (inj₁ l₀))

               inj₁l₀∈btl : (inj₁ l₀) ∈P btl
               inj₁l₀∈btl = pointwiseRespAny imp (proj₁ bl) (proj₁ btl) l₀∈bl (LPW.map ≈P-reflexive beql)
                 where 
                   imp : {l₀' : |L₀|} → {p : |P|} → l₀ ≈L₀ l₀' → p ≈P (inj₁ l₀') → inj₁ l₀ ≈P p
                   imp {l₀'} {p} l₀≈l₀' p≈inj₁l₀' = ≈P-trans (₁∼₁ l₀≈l₀') (≈P-sym p≈inj₁l₀') 

               ¬inj₁l₀⊑atl : ¬ Any (inj₁ l₀ ⊑P_) (proj₁ atl)
               ¬inj₁l₀⊑atl inj₁l₀⊑atl = ¬l₀⊑al l₀⊑al
                 where
                   imp : {l₀' : |L₀|} → {p : |P|} → inj₁ l₀ ⊑P p → p ≈P inj₁ l₀' → l₀ ⊑L₀ l₀' 
                   imp {l₀'} {p} inj₁l₀⊑p p≈inj₁l₀' with ⊑P-trans inj₁l₀⊑p (⊑P-reflexive p≈inj₁l₀')
                   imp {l₀'} {p} inj₁l₀⊑p p≈inj₁l₀' | ₁∼₁ l₀⊑l₀' = l₀⊑l₀'

                   l₀⊑al : Any (l₀ ⊑L₀_) (proj₁ al)
                   l₀⊑al = pointwiseRespAny⃖ imp (proj₁ al) (proj₁ atl) inj₁l₀⊑atl (LPW.map ≈P-reflexive aeql)
           inj₁l₀∈atl∨btl | inj₂ (inj₂ (l₀∈al , l₀∈bl)) = from ⟨$⟩ (inj₂ $ inj₂ (inj₁l₀∈atl , inj₁l₀∈btl)) 
             where
               open Equivalence (x∈∨⇔P∨-P atl btl (atl ∨F btl) (≈F-refl {atl ∨F btl}) (inj₁ l₀))

               inj₁l₀∈atl : (inj₁ l₀) ∈P atl
               inj₁l₀∈atl = pointwiseRespAny imp (proj₁ al) (proj₁ atl) l₀∈al (LPW.map ≈P-reflexive aeql)
                 where 
                   imp : {l₀' : |L₀|} → {p : |P|} → l₀ ≈L₀ l₀' → p ≈P (inj₁ l₀') → inj₁ l₀ ≈P p
                   imp {l₀'} {p} l₀≈l₀' p≈inj₁l₀' = ≈P-trans (₁∼₁ l₀≈l₀') (≈P-sym p≈inj₁l₀') 

               inj₁l₀∈btl : (inj₁ l₀) ∈P btl
               inj₁l₀∈btl = pointwiseRespAny imp (proj₁ bl) (proj₁ btl) l₀∈bl (LPW.map ≈P-reflexive beql)
                 where 
                   imp : {l₀' : |L₀|} → {p : |P|} → l₀ ≈L₀ l₀' → p ≈P (inj₁ l₀') → inj₁ l₀ ≈P p
                   imp {l₀'} {p} l₀≈l₀' p≈inj₁l₀' = ≈P-trans (₁∼₁ l₀≈l₀') (≈P-sym p≈inj₁l₀') 

           inj₁l₀∈jtl : (inj₁ l₀) ∈P jtl
           inj₁l₀∈jtl = p∈c1≈c2-P {inj₁ l₀} {atl ∨F btl} {jtl} (≈F-sym {jtl} {atl ∨F btl} jtl≈atl∨btl) inj₁l₀∈atl∨btl

           l₀∈jl : l₀ ∈L jl
           l₀∈jl = pointwiseRespAny⃖ imp (proj₁ jl) (proj₁ jtl) inj₁l₀∈jtl (LPW.map ≈P-reflexive jeql) 
             where
               imp : {l₀' : |L₀|} → {p : |P|} → inj₁ l₀ ≈P p → p ≈P inj₁ l₀' → l₀ ≈L₀ l₀'
               imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' with ≈P-trans inj₁l₀≈p p≈inj₁l₀'
               imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' | ₁∼₁ l₀≈l₀' = l₀≈l₀'

       --]]]

       sameElements : (l₀ : |L₀|) → (l₀ ∈L jl) ⇔ (l₀ ∈L (al ∨FL bl))
       sameElements l₀ = equivalence (l₀→ l₀) (l₀← l₀)
   --]]]

   jtr≈atr∨btr : jtr ≈F (atr ∨F btr)
   --[[[
   jtr≈atr∨btr = E-jtr≈atr.from ⟨$⟩ sameElements
     where
       module E-jtr≈atr = Equivalence (c1≈c2⇔sameElementsP jtr (atr ∨F btr))

       p→ : (p : |P|) → (p ∈P jtr) → (p ∈P (atr ∨F btr))
       --[[[
       p→ p p∈jtr = anyEliminate (proj₁ jr) elim z
         where
           open import Data.List.Membership.Setoid.Properties

           imp : {r₀ : |R₀|} → {x : |P|} → (p ≈P x) → (x ≈P inj₂ r₀) → (p ≈P inj₂ r₀)
           imp {l₀} {x} p≈x x≈inj₁r₀ = ≈P-trans p≈x x≈inj₁r₀

           jeqr' : LPW.Pointwise (λ x y → y ≈P inj₂ x) (proj₁ jr) (proj₁ jtr)
           jeqr' = LPW.reflexive ≈P-reflexive jeqr

           z : Any (λ r₀ → p ≈P inj₂ r₀) (proj₁ jr)
           z = pointwiseRespAny⃖ imp (proj₁ jr) (proj₁ jtr) p∈jtr jeqr'

           p∈jtl++jtr : p ∈P' (proj₁ jtl) ++ (proj₁ jtr)
           p∈jtl++jtr = ∈-++⁺ʳ ≈P-setoid (proj₁ jtl) p∈jtr

           p∈a∨b : p ∈P (a ∨F b)
           p∈a∨b = PE.subst (λ x → p ∈P' x) (PE.sym jconcat) p∈jtl++jtr

           elim : AnyEliminator {ℓQ = l0} |R₀| (p ∈P (atr ∨F btr)) (λ r₀ → p ≈P inj₂ r₀) (proj₁ jr)
           elim r₀ f p≈inj₂r₀ r₀∈jr with E.to ⟨$⟩ p∈a∨b   
             where
               module E = Equivalence (x∈∨⇔P∨-P a b (a ∨F b) (≈F-refl {a ∨F b}) p)
           elim r₀ f p≈inj₂r₀ r₀∈jr | inj₁ (p∈a , ¬p⊑b) with p∈atl⊎p∈atr
             where
               p∈atl++atr : p ∈P' (proj₁ atl) ++ (proj₁ atr)
               p∈atl++atr = PE.subst (λ x → p ∈P' x) aconcat p∈a

               p∈atl⊎p∈atr : (p ∈P atl) ⊎ (p ∈P atr)
               p∈atl⊎p∈atr = ∈-++⁻ ≈P-setoid (proj₁ atl) p∈atl++atr
           elim r₀ f p≈inj₂r₀ r₀∈jr | inj₁ (p∈a , ¬p⊑b) | inj₁ p∈atl =
             ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ al) (proj₁ atl) p∈atl (LPW.map ≈P-reflexive aeql) 
             where
               open import Data.List.Any.Properties
               module I = Inverse (⊥↔Any⊥ {xs = proj₁ al})

               imp' : {l₀ : |L₀|} → {p' : |P|} → (p ≈P p') → (p' ≈P inj₁ l₀) → const ⊥ l₀
               imp' {l₀} {p'} p≈p' p'≈inj₁l₀ with (≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀) 
                 where
                   p≈inj₁l₀ : p ≈P (inj₁ l₀)
                   p≈inj₁l₀ = ≈P-trans p≈p' p'≈inj₁l₀
               imp' {l₀} {p'} p≈p' p'≈inj₁l₀ | (₁∼₂ ())
           elim r₀ f p≈inj₂r₀ r₀∈jr | inj₁ (p∈a , ¬p⊑b) | inj₂ p∈atr = 
             from ⟨$⟩ inj₁ (p∈atr , ¬p⊑btr)
             where
               open Equivalence (x∈∨⇔P∨-P atr btr (atr ∨F btr) (≈F-refl {atr ∨F btr}) p)

               ¬p⊑btr : ¬ Any (p ⊑P_) (proj₁ btr)
               ¬p⊑btr p⊑btr = ¬p⊑b (++⁺ʳ (proj₁ btl) p⊑btr)
                 where
                   open import Data.List.Any.Properties           
           elim r₀ f p≈inj₂r₀ r₀∈jr | inj₂ (inj₁ (p∈b , ¬p⊑a)) with p∈btl⊎p∈btr
             where
               p∈btl++btr : p ∈P' (proj₁ btl) ++ (proj₁ btr)
               p∈btl++btr = PE.subst (λ x → p ∈P' x) bconcat p∈b

               p∈btl⊎p∈btr : (p ∈P btl) ⊎ (p ∈P btr)
               p∈btl⊎p∈btr = ∈-++⁻ ≈P-setoid (proj₁ btl) p∈btl++btr
           elim r₀ f p≈inj₂r₀ l₀∈jl | inj₂ (inj₁ (p∈b , ¬p⊑a)) | inj₁ p∈btl =
             ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ bl) (proj₁ btl) p∈btl (LPW.map ≈P-reflexive beql) 
             where
               open import Data.List.Any.Properties
               module I = Inverse (⊥↔Any⊥ {xs = proj₁ bl})

               imp' : {l₀ : |L₀|} → {p' : |P|} → (p ≈P p') → (p' ≈P inj₁ l₀) → const ⊥ l₀
               imp' {l₀} {p'} p≈p' p'≈inj₁l₀ with (≈P-trans (≈P-sym p≈inj₂r₀) p≈inj₁l₀) 
                 where
                   p≈inj₁l₀ : p ≈P (inj₁ l₀)
                   p≈inj₁l₀ = ≈P-trans p≈p' p'≈inj₁l₀
               imp' {l₀} {p'} p≈p' p'≈inj₁l₀ | ()    
           elim r₀ f p≈inj₂r₀ r₀∈jr | inj₂ (inj₁ (p∈b , ¬p⊑a)) | inj₂ p∈btr =
             from ⟨$⟩ inj₂ (inj₁ (p∈btr , ¬p⊑atr))
             where
               open Equivalence (x∈∨⇔P∨-P atr btr (atr ∨F btr) (≈F-refl {atr ∨F btr}) p)

               ¬p⊑atr : ¬ Any (p ⊑P_) (proj₁ atr)
               ¬p⊑atr p⊑atr = ¬p⊑a (++⁺ʳ (proj₁ atl) p⊑atr)
                 where
                   open import Data.List.Any.Properties      
           elim r₀ f p≈inj₂r₀ r₀∈jr | inj₂ (inj₂ (p∈a , p∈b)) with p∈atl⊎p∈atr | p∈btl⊎p∈btr
             where
               p∈atl++atr : p ∈P' (proj₁ atl) ++ (proj₁ atr)
               p∈atl++atr = PE.subst (λ x → p ∈P' x) aconcat p∈a

               p∈atl⊎p∈atr : (p ∈P atl) ⊎ (p ∈P atr)
               p∈atl⊎p∈atr = ∈-++⁻ ≈P-setoid (proj₁ atl) p∈atl++atr

               p∈btl++btr : p ∈P' (proj₁ btl) ++ (proj₁ btr)
               p∈btl++btr = PE.subst (λ x → p ∈P' x) bconcat p∈b

               p∈btl⊎p∈btr : (p ∈P btl) ⊎ (p ∈P btr)
               p∈btl⊎p∈btr = ∈-++⁻ ≈P-setoid (proj₁ btl) p∈btl++btr
           elim l₀ f p≈inj₂r₀ r₀∈jr | inj₂ (inj₂ (p∈a , p∈b)) | inj₂ p∈atr | inj₂ p∈btr =
             from ⟨$⟩ inj₂ (inj₂ (p∈atr , p∈btr))
             where
               open Equivalence (x∈∨⇔P∨-P atr btr (atr ∨F btr) (≈F-refl {atr ∨F btr}) p)
           elim l₀ f p≈inj₂r₀ r₀∈jr | inj₂ (inj₂ (p∈a , p∈b)) | inj₁ p∈atl | _ =
             ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ al) (proj₁ atl) p∈atl (LPW.map ≈P-reflexive aeql) 
             where
               open import Data.List.Any.Properties
               module I = Inverse (⊥↔Any⊥ {xs = proj₁ al})

               imp' : {l₀ : |L₀|} → {p' : |P|} → (p ≈P p') → (p' ≈P inj₁ l₀) → const ⊥ l₀
               imp' {l₀} {p'} p≈p' p'≈inj₁l₀ with (≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀) 
                 where
                   p≈inj₁l₀ : p ≈P (inj₁ l₀)
                   p≈inj₁l₀ = ≈P-trans p≈p' p'≈inj₁l₀
               imp' {l₀} {p'} p≈p' p'≈inj₁l₀ | (₁∼₂ ())
           elim l₀ f p≈inj₂r₀ r₀∈jr | inj₂ (inj₂ (p∈a , p∈b)) | _ | inj₁ p∈btl =
             ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ bl) (proj₁ btl) p∈btl (LPW.map ≈P-reflexive beql) 
             where
               open import Data.List.Any.Properties
               module I = Inverse (⊥↔Any⊥ {xs = proj₁ bl})

               imp' : {l₀ : |L₀|} → {p' : |P|} → (p ≈P p') → (p' ≈P inj₁ l₀) → const ⊥ l₀
               imp' {l₀} {p'} p≈p' p'≈inj₁l₀ with (≈P-trans (≈P-sym p≈inj₁l₀) p≈inj₂r₀) 
                 where
                   p≈inj₁l₀ : p ≈P (inj₁ l₀)
                   p≈inj₁l₀ = ≈P-trans p≈p' p'≈inj₁l₀
               imp' {r₀} {p'} p≈p' p'≈inj₁l₀ | (₁∼₂ ())       
           --]]]


       p← : (p : |P|) → (p ∈P (atr ∨F btr)) → (p ∈P jtr) 
       --[[[
       p← p p∈atr∨btr with to ⟨$⟩ p∈atr∨btr 
         where
           open Equivalence (x∈∨⇔P∨-P atr btr (atr ∨F btr) (≈F-refl {atr ∨F btr}) p)
       p← p p∈atr∨btr | inj₁ (p∈atr , ¬p⊑btr) = 
         anyEliminate (proj₁ ar) elim p≈inj₂ar
         where
           imp : {r₀ : |R₀|} → {p' : |P|} → p ≈P p' → p' ≈P (inj₂ r₀) → p ≈P inj₂ r₀
           imp {r₀} {p'} p≈p' p'≈inj₂r₀ = ≈P-trans p≈p' p'≈inj₂r₀

           p≈inj₂ar : Any (λ · → p ≈P inj₂ ·) (proj₁ ar)
           p≈inj₂ar = pointwiseRespAny⃖ imp (proj₁ ar) (proj₁ atr) p∈atr (LPW.map ≈P-reflexive aeqr)

           elim : AnyEliminator {ℓQ = l0} |R₀| (p ∈P jtr) (λ · → p ≈P inj₂ ·) (proj₁ ar)
           elim r₀ f p≈inj₂r₀ r₀∈ar = p∈jtr
             where
               open import Data.List.Any.Properties

               p∈a : p ∈P a
               p∈a = ++⁺ʳ (proj₁ atl) p∈atr

               ¬p⊑btl : ¬ Any (p ⊑P_) (proj₁ btl)
               --[[[
               ¬p⊑btl p⊑btl =
                 ⊥-elim $ from ⟨$⟩ (pointwiseRespAny⃖ imp' (proj₁ bl) (proj₁ btl) p⊑btl (LPW.map ≈P-reflexive beql)) 
                 where
                   open Inverse (⊥↔Any⊥ {xs = proj₁ bl})

                   imp' : {l₀ : |L₀|} → {p' : |P|} → p ⊑P p' → p' ≈P inj₁ l₀ → const ⊥ l₀
                   imp' {l₀} {p'} p⊑p' p'≈inj₁l₀ with inj₁l₀⊑inj₂r₀
                     where
                       open import Relation.Binary.PartialOrderReasoning (DecPoset.poset ⊑P-decPoset)

                       inj₁l₀⊑inj₂r₀ : inj₂ r₀ ⊑P inj₁ l₀
                       inj₁l₀⊑inj₂r₀ = begin
                         (inj₂ r₀) ≈⟨ ≈P-sym p≈inj₂r₀ ⟩
                         p ≤⟨ p⊑p' ⟩
                         p' ≈⟨ p'≈inj₁l₀ ⟩
                         (inj₁ l₀)
                        ∎
                   imp' {r₀} {p'} p⊑p' p'≈inj₂r₀ | ()
               --]]]

               ¬p⊑b : ¬ Any (p ⊑P_) ((proj₁ btl) ++ (proj₁ btr))
               ¬p⊑b p⊑btl++btr with ++⁻ (proj₁ btl) p⊑btl++btr
               ¬p⊑b p⊑btl++btr | inj₁ p⊑btl = ¬p⊑btl p⊑btl
               ¬p⊑b p⊑btl++btr | inj₂ p⊑btr = ¬p⊑btr p⊑btr

               open Equivalence (x∈∨⇔P∨-P a b (a ∨F b) (≈F-refl {a ∨F b}) p)

               p∈a∨b : p ∈P (a ∨F b)
               p∈a∨b = from ⟨$⟩ inj₁ (p∈a , ¬p⊑b)  

               p∈jtl++jtr : p ∈P' (proj₁ jtl ++ proj₁ jtr)
               p∈jtl++jtr = PE.subst (λ · → p ∈P' ·) jconcat p∈a∨b

               p∈jtr : p ∈P' (proj₁ jtr)
               --[[[
               p∈jtr with ++⁻ (proj₁ jtl) p∈jtl++jtr
               p∈jtr | inj₁ p∈jtl = 
                 ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ jl) (proj₁ jtl) p∈jtl (LPW.map ≈P-reflexive jeql) 
                 where
                   module I = Inverse (⊥↔Any⊥ {xs = proj₁ jl})

                   imp' : {l₀ : |L₀|} → {p' : |P|} → p ≈P p' → p' ≈P inj₁ l₀ → const ⊥ l₀
                   imp' {l₀} {p'} p≈p' p'≈inj₁l₀ with inj₁l₀≈inj₂r₀ 
                     where
                       open import Relation.Binary.EqReasoning (≈P-setoid)

                       inj₁l₀≈inj₂r₀ : (inj₁ l₀) ≈P (inj₂ r₀)
                       inj₁l₀≈inj₂r₀ = 
                         begin
                           inj₁ l₀ ≈⟨ ≈P-sym p'≈inj₁l₀ ⟩
                           p' ≈⟨ ≈P-sym p≈p' ⟩
                           p ≈⟨ p≈inj₂r₀ ⟩
                           inj₂ r₀
                          ∎ 
                   imp' {r₀} {p'} p≈p' p'≈inj₁l₀ | ₁∼₂ ()
               p∈jtr | inj₂ goal = goal
               --]]]
       p← p p∈atr∨btr | inj₂ (inj₁ (p∈btr , ¬p⊑atr)) = 
         anyEliminate (proj₁ br) elim p≈inj₂br
         where
           imp : {r₀ : |R₀|} → {p' : |P|} → p ≈P p' → p' ≈P (inj₂ r₀) → p ≈P inj₂ r₀
           imp {r₀} {p'} p≈p' p'≈inj₂r₀ = ≈P-trans p≈p' p'≈inj₂r₀

           p≈inj₂br : Any (λ · → p ≈P inj₂ ·) (proj₁ br)
           p≈inj₂br = pointwiseRespAny⃖ imp (proj₁ br) (proj₁ btr) p∈btr (LPW.map ≈P-reflexive beqr)

           elim : AnyEliminator {ℓQ = l0} |R₀| (p ∈P jtr) (λ · → p ≈P inj₂ ·) (proj₁ br)
           elim r₀ f p≈inj₂r₀ r₀∈ar = p∈jtr
             where
               open import Data.List.Any.Properties

               p∈b : p ∈P b
               p∈b = ++⁺ʳ (proj₁ btl) p∈btr

               ¬p⊑atl : ¬ Any (p ⊑P_) (proj₁ atl)
               --[[[
               ¬p⊑atl p⊑atl =
                 ⊥-elim $ from ⟨$⟩ (pointwiseRespAny⃖ imp' (proj₁ al) (proj₁ atl) p⊑atl (LPW.map ≈P-reflexive aeql)) 
                 where
                   open Inverse (⊥↔Any⊥ {xs = proj₁ al})

                   imp' : {l₀ : |L₀|} → {p' : |P|} → p ⊑P p' → p' ≈P inj₁ l₀ → const ⊥ l₀
                   imp' {l₀} {p'} p⊑p' p'≈inj₁l₀ with inj₁l₀⊑inj₂r₀
                     where
                       open import Relation.Binary.PartialOrderReasoning (DecPoset.poset ⊑P-decPoset)

                       inj₁l₀⊑inj₂r₀ : inj₂ r₀ ⊑P inj₁ l₀
                       inj₁l₀⊑inj₂r₀ = begin
                         (inj₂ r₀) ≈⟨ ≈P-sym p≈inj₂r₀ ⟩
                         p ≤⟨ p⊑p' ⟩
                         p' ≈⟨ p'≈inj₁l₀ ⟩
                         (inj₁ l₀)
                        ∎
                   imp' {r₀} {p'} p⊑p' p'≈inj₂r₀ | ()
               --]]]

               ¬p⊑a : ¬ Any (p ⊑P_) ((proj₁ atl) ++ (proj₁ atr))
               ¬p⊑a p⊑atl++atr with ++⁻ (proj₁ atl) p⊑atl++atr
               ¬p⊑a p⊑atl++atr | inj₁ p⊑atl = ¬p⊑atl p⊑atl
               ¬p⊑a p⊑atl++atr | inj₂ p⊑atr = ¬p⊑atr p⊑atr

               open Equivalence (x∈∨⇔P∨-P a b (a ∨F b) (≈F-refl {a ∨F b}) p)

               p∈a∨b : p ∈P (a ∨F b)
               p∈a∨b = from ⟨$⟩ (inj₂ (inj₁ (p∈b , ¬p⊑a)))  

               p∈jtl++jtr : p ∈P' (proj₁ jtl ++ proj₁ jtr)
               p∈jtl++jtr = PE.subst (λ · → p ∈P' ·) jconcat p∈a∨b

               p∈jtr : p ∈P' (proj₁ jtr)
               --[[[
               p∈jtr with ++⁻ (proj₁ jtl) p∈jtl++jtr
               p∈jtr | inj₁ p∈jtl = 
                 ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ jl) (proj₁ jtl) p∈jtl (LPW.map ≈P-reflexive jeql) 
                 where
                   module I = Inverse (⊥↔Any⊥ {xs = proj₁ jl})

                   imp' : {l₀ : |L₀|} → {p' : |P|} → p ≈P p' → p' ≈P inj₁ l₀ → const ⊥ l₀
                   imp' {l₀} {p'} p≈p' p'≈inj₁l₀ with inj₁l₀≈inj₂r₀ 
                     where
                       open import Relation.Binary.EqReasoning (≈P-setoid)

                       inj₁l₀≈inj₂r₀ : (inj₁ l₀) ≈P (inj₂ r₀)
                       inj₁l₀≈inj₂r₀ = 
                         begin
                           inj₁ l₀ ≈⟨ ≈P-sym p'≈inj₁l₀ ⟩
                           p' ≈⟨ ≈P-sym p≈p' ⟩
                           p ≈⟨ p≈inj₂r₀ ⟩
                           inj₂ r₀
                          ∎ 
                   imp' {r₀} {p'} p≈p' p'≈inj₁l₀ | ₁∼₂ ()
               p∈jtr | inj₂ goal = goal
               --]]]
       p← p p∈atr∨btr | inj₂ (inj₂ (p∈atr , p∈btr)) = 
         anyEliminate (proj₁ br) elim p≈inj₂br
         where
           imp : {r₀ : |R₀|} → {p' : |P|} → p ≈P p' → p' ≈P (inj₂ r₀) → p ≈P inj₂ r₀
           imp {r₀} {p'} p≈p' p'≈inj₂r₀ = ≈P-trans p≈p' p'≈inj₂r₀

           p≈inj₂br : Any (λ · → p ≈P inj₂ ·) (proj₁ br)
           p≈inj₂br = pointwiseRespAny⃖ imp (proj₁ br) (proj₁ btr) p∈btr (LPW.map ≈P-reflexive beqr)

           elim : AnyEliminator {ℓQ = l0} |R₀| (p ∈P jtr) (λ · → p ≈P inj₂ ·) (proj₁ br)
           elim r₀ f p≈inj₂r₀ r₀∈ar = p∈jtr
             where
               open import Data.List.Any.Properties

               p∈a : p ∈P a
               p∈a = ++⁺ʳ (proj₁ atl) p∈atr

               p∈b : p ∈P b
               p∈b = ++⁺ʳ (proj₁ btl) p∈btr

               open Equivalence (x∈∨⇔P∨-P a b (a ∨F b) (≈F-refl {a ∨F b}) p)

               p∈a∨b : p ∈P (a ∨F b)
               p∈a∨b = from ⟨$⟩ (inj₂ (inj₂ (p∈a , p∈b)))  

               p∈jtl++jtr : p ∈P' (proj₁ jtl ++ proj₁ jtr)
               p∈jtl++jtr = PE.subst (λ · → p ∈P' ·) jconcat p∈a∨b

               p∈jtr : p ∈P' (proj₁ jtr)
               --[[[
               p∈jtr with ++⁻ (proj₁ jtl) p∈jtl++jtr
               p∈jtr | inj₁ p∈jtl = 
                 ⊥-elim $ I.from ⟨$⟩ pointwiseRespAny⃖ imp' (proj₁ jl) (proj₁ jtl) p∈jtl (LPW.map ≈P-reflexive jeql) 
                 where
                   module I = Inverse (⊥↔Any⊥ {xs = proj₁ jl})

                   imp' : {l₀ : |L₀|} → {p' : |P|} → p ≈P p' → p' ≈P inj₁ l₀ → const ⊥ l₀
                   imp' {l₀} {p'} p≈p' p'≈inj₁l₀ with inj₁l₀≈inj₂r₀ 
                     where
                       open import Relation.Binary.EqReasoning (≈P-setoid)

                       inj₁l₀≈inj₂r₀ : (inj₁ l₀) ≈P (inj₂ r₀)
                       inj₁l₀≈inj₂r₀ = 
                         begin
                           inj₁ l₀ ≈⟨ ≈P-sym p'≈inj₁l₀ ⟩
                           p' ≈⟨ ≈P-sym p≈p' ⟩
                           p ≈⟨ p≈inj₂r₀ ⟩
                           inj₂ r₀
                          ∎ 
                   imp' {r₀} {p'} p≈p' p'≈inj₁l₀ | ₁∼₂ ()
               p∈jtr | inj₂ goal = goal
               --]]]
       --]]]


       sameElements : (p : |P|) → (p ∈P jtr) ⇔ (p ∈P (atr ∨F btr))
       sameElements p = equivalence (p→ p) (p← p)
   --]]]

   jr≈ar∨br : jr ≈FR (ar ∨FR br)
   --[[[
   jr≈ar∨br = E.from ⟨$⟩ sameElements 
     where
       module E = Equivalence (c1≈c2⇔sameElementsR jr (ar ∨FR br))

       r₀→ : (r₀ : |R₀|) → (r₀ ∈R jr) → (r₀ ∈R (ar ∨FR br))
       --[[[
       r₀→ r₀ r₀∈jr with to ⟨$⟩ inj₂r₀∈atr∨btr  
         where
           open Equivalence (x∈∨⇔P∨-P atr btr (atr ∨F btr) (≈F-refl {atr ∨F btr}) (inj₂ r₀))

           inj₂r₀∈jtr : (inj₂ r₀) ∈P jtr
           inj₂r₀∈jtr = pointwiseRespAny imp (proj₁ jr) (proj₁ jtr) r₀∈jr (LPW.reflexive ≈P-reflexive jeqr)
             where
               imp : {r₀' : |R₀|} → {p : |P|} → r₀ ≈R₀ r₀' → p ≈P inj₂ r₀' → (inj₂ r₀ ≈P p)
               imp {r₀'} {p} r₀≈r₀' p≈inj₂r₀' = ≈P-sym (≈P-trans p≈inj₂r₀' (₂∼₂ $ ≈R₀-sym r₀≈r₀'))

           inj₂r₀∈atr∨btr : (inj₂ r₀) ∈P (atr ∨F btr)
           inj₂r₀∈atr∨btr = p∈c1≈c2-P {inj₂ r₀} {jtr} {atr ∨F btr} jtr≈atr∨btr inj₂r₀∈jtr

       r₀→ r₀ r₀∈jl | inj₁ (inj₂r₀∈atr , ¬inj₂r₀⊑btr) = 
         from ⟨$⟩ inj₁ (r₀∈ar , ¬r₀⊑br)
         where
           open Equivalence (x∈∨⇔P∨-R ar br (ar ∨FR br) (≈FR-refl {ar ∨FR br}) r₀)

           r₀∈ar : r₀ ∈R ar
           r₀∈ar = pointwiseRespAny⃖ imp (proj₁ ar) (proj₁ atr) inj₂r₀∈atr (LPW.map ≈P-reflexive aeqr)
             where
               imp : {r₀' : |R₀|} → {p : |P|} → inj₂ r₀ ≈P p → p ≈P inj₂ r₀' → r₀ ≈R₀ r₀'
               imp {r₀'} {p} inj₂r₀≈p p≈inj₂r₀' with ≈P-trans inj₂r₀≈p p≈inj₂r₀'
               imp {r₀'} {p} inj₂r₀≈p p≈inj₂r₀' | ₂∼₂ r₀≈r₀' = r₀≈r₀'

           ¬r₀⊑br : ¬ Any (r₀ ⊑R₀_) (proj₁ br)
           ¬r₀⊑br r₀⊑br = ¬inj₂r₀⊑btr inj₂r₀⊑btr
             where
               inj₂r₀⊑btr : Any (inj₂ r₀ ⊑P_) (proj₁ btr)
               inj₂r₀⊑btr = pointwiseRespAny imp (proj₁ br) (proj₁ btr) r₀⊑br (LPW.map ≈P-reflexive beqr)
                 where
                   imp : {r₀' : |R₀|} → {p : |P|} → r₀ ⊑R₀ r₀' → p ≈P inj₂ r₀' → inj₂ r₀ ⊑P p
                   imp {r₀'} {p} r₀⊑r₀' p≈inj₂r₀' = ⊑P-trans (₂∼₂ r₀⊑r₀') (⊑P-reflexive (≈P-sym p≈inj₂r₀'))
       r₀→ r₀ r₀∈jr | inj₂ (inj₁ (inj₂r₀∈btr , ¬inj₂r₀⊑atr)) =
         from ⟨$⟩ inj₂ (inj₁ (r₀∈br , ¬r₀⊑ar))
         where
           open Equivalence (x∈∨⇔P∨-R ar br (ar ∨FR br) (≈FR-refl {ar ∨FR br}) r₀)

           r₀∈br : r₀ ∈R br
           r₀∈br = pointwiseRespAny⃖ imp (proj₁ br) (proj₁ btr) inj₂r₀∈btr (LPW.map ≈P-reflexive beqr)
             where
               imp : {r₀' : |R₀|} → {p : |P|} → inj₂ r₀ ≈P p → p ≈P inj₂ r₀' → r₀ ≈R₀ r₀'
               imp {r₀'} {p} inj₂r₀≈p p≈inj₂r₀' with ≈P-trans inj₂r₀≈p p≈inj₂r₀'
               imp {r₀'} {p} inj₂r₀≈p p≈inj₂r₀' | ₂∼₂ r₀≈r₀' = r₀≈r₀'

           ¬r₀⊑ar : ¬ Any (r₀ ⊑R₀_) (proj₁ ar)
           ¬r₀⊑ar r₀⊑ar = ¬inj₂r₀⊑atr inj₂r₀⊑atr
             where
               inj₂r₀⊑atr : Any (inj₂ r₀ ⊑P_) (proj₁ atr)
               inj₂r₀⊑atr = pointwiseRespAny imp (proj₁ ar) (proj₁ atr) r₀⊑ar (LPW.map ≈P-reflexive aeqr)
                 where
                   imp : {r₀' : |R₀|} → {p : |P|} → r₀ ⊑R₀ r₀' → p ≈P inj₂ r₀' → inj₂ r₀ ⊑P p
                   imp {r₀'} {p} r₀⊑r₀' p≈inj₂r₀' = ⊑P-trans (₂∼₂ r₀⊑r₀') (⊑P-reflexive (≈P-sym p≈inj₂r₀'))

       r₀→ r₀ r₀∈jr | inj₂ (inj₂ (inj₂r₀∈atr , inj₂r₀∈btr)) =
         from ⟨$⟩ inj₂ (inj₂ (r₀∈ar , r₀∈br))
         where
           open Equivalence (x∈∨⇔P∨-R ar br (ar ∨FR br) (≈FR-refl {ar ∨FR br}) r₀)

           r₀∈ar : r₀ ∈R ar
           r₀∈ar = pointwiseRespAny⃖ imp (proj₁ ar) (proj₁ atr) inj₂r₀∈atr (LPW.map ≈P-reflexive aeqr)
             where
               imp : {r₀' : |R₀|} → {p : |P|} → inj₂ r₀ ≈P p → p ≈P inj₂ r₀' → r₀ ≈R₀ r₀'
               imp {r₀'} {p} inj₁r₀≈p p≈inj₁r₀' with ≈P-trans inj₁r₀≈p p≈inj₁r₀'
               imp {r₀'} {p} inj₁r₀≈p p≈inj₁r₀' | ₂∼₂ r₀≈r₀' = r₀≈r₀'

           r₀∈br : r₀ ∈R br
           r₀∈br = pointwiseRespAny⃖ imp (proj₁ br) (proj₁ btr) inj₂r₀∈btr (LPW.map ≈P-reflexive beqr)
             where
               imp : {r₀' : |R₀|} → {p : |P|} → inj₂ r₀ ≈P p → p ≈P inj₂ r₀' → r₀ ≈R₀ r₀'
               imp {r₀'} {p} inj₂r₀≈p p≈inj₂r₀' with ≈P-trans inj₂r₀≈p p≈inj₂r₀'
               imp {r₀'} {p} inj₂r₀≈p p≈inj₂r₀' | ₂∼₂ r₀≈r₀' = r₀≈r₀'
       --]]]    


       r₀← : (r₀ : |R₀|) → (r₀ ∈R (ar ∨FR br)) → (r₀ ∈R jr)
       --[[[
       r₀← r₀ r₀∈ar∨br = r₀∈jr
         where
           inj₂r₀∈atr∨btr : (inj₂ r₀) ∈P (atr ∨F btr)
           inj₂r₀∈atr∨btr with to ⟨$⟩ r₀∈ar∨br
             where
               open Equivalence (x∈∨⇔P∨-R ar br (ar ∨FR br) (≈FR-refl {ar ∨FR br}) r₀)
           inj₂r₀∈atr∨btr | inj₁ (r₀∈ar , ¬r₀⊑br) = from ⟨$⟩ inj₁ (inj₂r₀∈atr , ¬inj₂r₀⊑btr)
             where
               open Equivalence (x∈∨⇔P∨-P atr btr (atr ∨F btr) (≈F-refl {atr ∨F btr}) (inj₂ r₀))

               inj₂r₀∈atr : (inj₂ r₀) ∈P atr
               inj₂r₀∈atr = pointwiseRespAny imp (proj₁ ar) (proj₁ atr) r₀∈ar (LPW.map ≈P-reflexive aeqr)
                 where 
                   imp : {r₀' : |R₀|} → {p : |P|} → r₀ ≈R₀ r₀' → p ≈P (inj₂ r₀') → inj₂ r₀ ≈P p
                   imp {r₀'} {p} r₀≈r₀' p≈inj₂r₀' = ≈P-trans (₂∼₂ r₀≈r₀') (≈P-sym p≈inj₂r₀') 

               ¬inj₂r₀⊑btr : ¬ Any (inj₂ r₀ ⊑P_) (proj₁ btr)
               ¬inj₂r₀⊑btr inj₂r₀⊑btr = ¬r₀⊑br r₀⊑br
                 where
                   imp : {r₀' : |R₀|} → {p : |P|} → inj₂ r₀ ⊑P p → p ≈P inj₂ r₀' → r₀ ⊑R₀ r₀' 
                   imp {r₀'} {p} inj₂r₀⊑p p≈inj₂r₀' with ⊑P-trans inj₂r₀⊑p (⊑P-reflexive p≈inj₂r₀')
                   imp {r₀'} {p} inj₂r₀⊑p p≈inj₂r₀' | ₂∼₂ r₀⊑r₀' = r₀⊑r₀'

                   r₀⊑br : Any (r₀ ⊑R₀_) (proj₁ br)
                   r₀⊑br = pointwiseRespAny⃖ imp (proj₁ br) (proj₁ btr) inj₂r₀⊑btr (LPW.map ≈P-reflexive beqr)
           inj₂r₀∈atr∨btr | inj₂ (inj₁ (r₀∈br , ¬r₀⊑ar)) = from ⟨$⟩ (inj₂ $ inj₁ (inj₂r₀∈btr , ¬inj₂r₀⊑atr)) 
             where
               open Equivalence (x∈∨⇔P∨-P atr btr (atr ∨F btr) (≈F-refl {atr ∨F btr}) (inj₂ r₀))

               inj₂r₀∈btr : (inj₂ r₀) ∈P btr
               inj₂r₀∈btr = pointwiseRespAny imp (proj₁ br) (proj₁ btr) r₀∈br (LPW.map ≈P-reflexive beqr)
                 where 
                   imp : {r₀' : |R₀|} → {p : |P|} → r₀ ≈R₀ r₀' → p ≈P (inj₂ r₀') → inj₂ r₀ ≈P p
                   imp {r₀'} {p} r₀≈r₀' p≈inj₂r₀' = ≈P-trans (₂∼₂ r₀≈r₀') (≈P-sym p≈inj₂r₀') 

               ¬inj₂r₀⊑atr : ¬ Any (inj₂ r₀ ⊑P_) (proj₁ atr)
               ¬inj₂r₀⊑atr inj₂r₀⊑atr = ¬r₀⊑ar r₀⊑ar
                 where
                   imp : {r₀' : |R₀|} → {p : |P|} → inj₂ r₀ ⊑P p → p ≈P inj₂ r₀' → r₀ ⊑R₀ r₀' 
                   imp {r₀'} {p} inj₂r₀⊑p p≈inj₂r₀' with ⊑P-trans inj₂r₀⊑p (⊑P-reflexive p≈inj₂r₀')
                   imp {r₀'} {p} inj₂r₀⊑p p≈inj₂r₀' | ₂∼₂ r₀⊑r₀' = r₀⊑r₀'

                   r₀⊑ar : Any (r₀ ⊑R₀_) (proj₁ ar)
                   r₀⊑ar = pointwiseRespAny⃖ imp (proj₁ ar) (proj₁ atr) inj₂r₀⊑atr (LPW.map ≈P-reflexive aeqr)
           inj₂r₀∈atr∨btr | inj₂ (inj₂ (r₀∈ar , r₀∈br)) = from ⟨$⟩ (inj₂ $ inj₂ (inj₂r₀∈atr , inj₂r₀∈btr)) 
             where
               open Equivalence (x∈∨⇔P∨-P atr btr (atr ∨F btr) (≈F-refl {atr ∨F btr}) (inj₂ r₀))

               inj₂r₀∈atr : (inj₂ r₀) ∈P atr
               inj₂r₀∈atr = pointwiseRespAny imp (proj₁ ar) (proj₁ atr) r₀∈ar (LPW.map ≈P-reflexive aeqr)
                 where 
                   imp : {r₀' : |R₀|} → {p : |P|} → r₀ ≈R₀ r₀' → p ≈P (inj₂ r₀') → inj₂ r₀ ≈P p
                   imp {r₀'} {p} r₀≈r₀' p≈inj₂r₀' = ≈P-trans (₂∼₂ r₀≈r₀') (≈P-sym p≈inj₂r₀') 

               inj₂r₀∈btr : (inj₂ r₀) ∈P btr
               inj₂r₀∈btr = pointwiseRespAny imp (proj₁ br) (proj₁ btr) r₀∈br (LPW.map ≈P-reflexive beqr)
                 where 
                   imp : {r₀' : |R₀|} → {p : |P|} → r₀ ≈R₀ r₀' → p ≈P (inj₂ r₀') → inj₂ r₀ ≈P p
                   imp {r₀'} {p} r₀≈r₀' p≈inj₂r₀' = ≈P-trans (₂∼₂ r₀≈r₀') (≈P-sym p≈inj₂r₀') 

           inj₂r₀∈jtr : (inj₂ r₀) ∈P jtr
           inj₂r₀∈jtr = p∈c1≈c2-P {inj₂ r₀} {atr ∨F btr} {jtr} (≈F-sym {jtr} {atr ∨F btr} jtr≈atr∨btr) inj₂r₀∈atr∨btr

           r₀∈jr : r₀ ∈R jr
           r₀∈jr = pointwiseRespAny⃖ imp (proj₁ jr) (proj₁ jtr) inj₂r₀∈jtr (LPW.map ≈P-reflexive jeqr) 
             where
               imp : {r₀' : |R₀|} → {p : |P|} → inj₂ r₀ ≈P p → p ≈P inj₂ r₀' → r₀ ≈R₀ r₀'
               imp {r₀'} {p} inj₂r₀≈p p≈inj₂r₀' with ≈P-trans inj₂r₀≈p p≈inj₂r₀'
               imp {r₀'} {p} inj₂r₀≈p p≈inj₂r₀' | ₂∼₂ r₀≈r₀' = r₀≈r₀'
       --]]]

       sameElements : (r₀ : |R₀|) → (r₀ ∈R jr) ⇔ (r₀ ∈R (ar ∨FR br))
       sameElements r₀ = equivalence (r₀→ r₀) (r₀← r₀)
   --]]]


--]]]

inv-FP→S→FP : (a : Carrier-FP) → ((|f| $ |g| a) ≈F a) 
--[[[
inv-FP→S→FP a =
  ≈F-sym {a} {|f| $ |g| a} (EP.from ⟨$⟩ sameElements)
  where
    open import Relation.Binary.EqReasoning FP-setoid
    module EP = Equivalence (c1≈c2⇔sameElementsP a (|f| $ |g| a))

    l : Carrier-FPL
    l = proj₁ (decompose a)

    r : Carrier-FPR
    r = let _ , r , _ , _ , _ , _ , _ = decompose a in r

    al : Carrier-FP
    al = let _ , _ , al , _ , _ , _ , _ = decompose a in al

    ar : Carrier-FP
    ar = let _ , _ , _ , ar , _ , _ , _ = decompose a in ar

    eql = let _ , _ , _ , _ , eql , _ , _ = decompose a in eql
    eqr = let _ , _ , _ , _ , _ , eqr , _ = decompose a in eqr

    aconcat : (proj₁ a) ≡ (proj₁ al) ++ (proj₁ ar)
    aconcat = let _ , _ , _ , _ , _ , _ , aconcat = decompose a in aconcat

    p→ : (p : |P|) → (p ∈P (|f| $ |g| a)) → p ∈P a
    --[[[

    p→ p p∈fga with to ⟨$⟩ p∈fga
      where
        open Equivalence (|f|-prop (|g| a) p) 
    p→ p p∈fga | inj₁ (l₀ , p≈inj₁l₀ , l₀∈fLgLl) =
      p∈a  
      where
        open import Data.List.Membership.Setoid.Properties
        imp : {x : |L₀|} → {y : |P|} → l₀ ≈L₀ x → y ≡ inj₁ x → ((inj₁ l₀) ≈P y) 
        imp {x} {y} l₀≈x y≡inj₁x = ≈P-sym $ ≈P-trans (≈P-reflexive y≡inj₁x) (₁∼₁ $ ≈L₀-sym l₀≈x)

        fLgLl≈l : |fL| (|gL| l) ≈FL l
        fLgLl≈l = L-inv-FP→S→FP l

        l₀∈l : l₀ ∈L l
        l₀∈l = goal 
          where
            sameElements : (z : |L₀|) → (z ∈L (|fL| $ |gL| $ l)) ⇔ (z ∈L l)
            sameElements = to ⟨$⟩ fLgLl≈l
              where
                open Equivalence (c1≈c2⇔sameElementsL (|fL| $ |gL| l) l)

            goal : l₀ ∈L l 
            goal = to ⟨$⟩ l₀∈fLgLl 
              where
                open Equivalence (sameElements l₀)

        p∈al : p ∈P al
        p∈al = ∈-resp-≈ ≈P-setoid (≈P-sym p≈inj₁l₀) (pointwiseRespAny imp (proj₁ l) (proj₁ al) l₀∈l eql)

        p∈al++ar : p ∈P' (proj₁ al ++ proj₁ ar) 
        p∈al++ar = ∈-++⁺ˡ ≈P-setoid p∈al
        
        p∈a : p ∈P a
        p∈a = PE.subst (λ · → p ∈P' ·) (PE.sym aconcat) p∈al++ar 
    p→ p p∈fga | inj₂ (r₀ , p≈inj₂r₀ , r₀∈fRgRr) =
      p∈a  
      where
        open import Data.List.Membership.Setoid.Properties
        imp : {x : |R₀|} → {y : |P|} → r₀ ≈R₀ x → y ≡ inj₂ x → ((inj₂ r₀) ≈P y) 
        imp {x} {y} r₀≈x y≡inj₂x = ≈P-sym $ ≈P-trans (≈P-reflexive y≡inj₂x) (₂∼₂ $ ≈R₀-sym r₀≈x)

        fRgRr≈r : |fR| (|gR| r) ≈FR r
        fRgRr≈r = R-inv-FP→S→FP r

        r₀∈r : r₀ ∈R r
        r₀∈r = goal 
          where
            sameElements : (z : |R₀|) → (z ∈R (|fR| $ |gR| $ r)) ⇔ (z ∈R r)
            sameElements = to ⟨$⟩ fRgRr≈r
              where
                open Equivalence (c1≈c2⇔sameElementsR (|fR| $ |gR| r) r)

            goal : r₀ ∈R r
            goal = to ⟨$⟩ r₀∈fRgRr 
              where
                open Equivalence (sameElements r₀)

        p∈ar : p ∈P ar
        p∈ar = ∈-resp-≈ ≈P-setoid (≈P-sym p≈inj₂r₀) (pointwiseRespAny imp (proj₁ r) (proj₁ ar) r₀∈r eqr)

        p∈al++ar : p ∈P' (proj₁ al) ++ (proj₁ ar)
        p∈al++ar = ∈-++⁺ʳ ≈P-setoid (proj₁ al) p∈ar

        p∈a : p ∈P a
        p∈a = PE.subst (λ · → p ∈P' ·) (PE.sym aconcat) p∈al++ar 
    --]]]

    p← : (p : |P|) → (p ∈P a) → (p ∈P (|f| $ |g| a))
    --[[[

    p← (inj₁ l₀) inj₁l₀∈a = 
      E3.from ⟨$⟩ inj₁ (l₀ , (≈P-reflexive PE.refl) , l₀∈fLgLl)
      where
        open import Data.List.Membership.Setoid.Properties
        module E1 = Equivalence (c1≈c2⇔sameElementsL (|fL| $ |gL| l) l)
        module E2 = Equivalence ((E1.to ⟨$⟩ L-inv-FP→S→FP l) l₀) 

        inj₁l₀∈al : inj₁ l₀ ∈P al
        --[[[
        inj₁l₀∈al = anyEliminate (proj₁ al ++ proj₁ ar) eliminator inj₁l₀∈al++ar  
          where
            inj₁l₀∈al++ar : inj₁ l₀ ∈P' (proj₁ al) ++ (proj₁ ar)
            inj₁l₀∈al++ar = PE.subst (λ · → inj₁ l₀ ∈P' ·) aconcat inj₁l₀∈a

            eliminator : AnyEliminator {ℓQ = l0} |P| (inj₁ l₀ ∈P al) (inj₁ l₀ ≈P_) (proj₁ al ++ proj₁ ar)
            eliminator x f inj₁l₀≈x x∈≡a with ∈-++⁻ ≈P-setoid (proj₁ al) (LAny.map (λ x≡· → ≈P-reflexive x≡·) x∈≡a)
            eliminator x f inj₁l₀≈x x∈≡a | inj₁ x∈proj₁al =
              ∈-resp-≈ ≈P-setoid (≈P-sym inj₁l₀≈x) x∈proj₁al
            eliminator x f inj₁l₀≈x x∈≡a | inj₂ x∈proj₁ar =
               ⊥-elim (from ⟨$⟩ pointwiseRespAny⃖ imp (proj₁ r) (proj₁ ar) x∈proj₁ar (LPW.map ≈P-reflexive eqr)) 
              where 
                open import Data.List.Any.Properties
                open Inverse (⊥↔Any⊥ {A = |R₀|} {xs = proj₁ r})

                imp : {r₀ : |R₀|} → {p : |P|} → (x ≈P p) → (p ≈P inj₂ r₀) → const ⊥ r₀
                imp {r₀} {p} x≈p p≈inj₂r₀ with ≈P-trans inj₁l₀≈x (≈P-trans x≈p p≈inj₂r₀)
                imp {r₀} {p} x≈p p≈inj₂r₀ | ₁∼₂ ()
        --]]]

        l₀∈l : l₀ ∈L l
        l₀∈l = pointwiseRespAny⃖ imp (proj₁ l) (proj₁ al) inj₁l₀∈al (LPW.map ≈P-reflexive eql) 
          where
            imp : {l₀' : |L₀|} → {p : |P|} → (inj₁ l₀ ≈P p) →  (p ≈P inj₁ l₀') → (l₀ ≈L₀ l₀')
            imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' with (≈P-trans inj₁l₀≈p p≈inj₁l₀')
            imp {l₀'} {p} inj₁l₀≈p p≈inj₁l₀' | ₁∼₁ l₀≈l₀' = l₀≈l₀'

        l₀∈fLgLl : l₀ ∈L (|fL| $ |gL| l)
        l₀∈fLgLl = E2.from ⟨$⟩ l₀∈l

        module E3 = Equivalence (|f|-prop (|g| a) (inj₁ l₀))
    p← (inj₂ r₀) inj₂r₀∈a =
      E3.from ⟨$⟩ inj₂ (r₀ , (≈P-reflexive PE.refl) , r₀∈fRgRr)
      where
        open import Data.List.Membership.Setoid.Properties
        module E1 = Equivalence (c1≈c2⇔sameElementsR (|fR| $ |gR| r) r)
        module E2 = Equivalence ((E1.to ⟨$⟩ R-inv-FP→S→FP r) r₀) 

        inj₂r₀∈ar : inj₂ r₀ ∈P ar
        --[[[
        inj₂r₀∈ar = anyEliminate (proj₁ al ++ proj₁ ar) eliminator inj₂r₀∈al++ar  
          where
            inj₂r₀∈al++ar : inj₂ r₀ ∈P' (proj₁ al) ++ (proj₁ ar)
            inj₂r₀∈al++ar = PE.subst (λ · → inj₂ r₀ ∈P' ·) aconcat inj₂r₀∈a

            eliminator : AnyEliminator {ℓQ = l0} |P| (inj₂ r₀ ∈P ar) (inj₂ r₀ ≈P_) (proj₁ al ++ proj₁ ar)
            eliminator x f inj₂r₀≈x x∈≡a with ∈-++⁻ ≈P-setoid (proj₁ al) (LAny.map (λ x≡· → ≈P-reflexive x≡·) x∈≡a)
            eliminator x f inj₂r₀≈x x∈≡a | inj₁ x∈proj₁al =
              ⊥-elim (from ⟨$⟩ pointwiseRespAny⃖ imp (proj₁ l) (proj₁ al) x∈proj₁al (LPW.map ≈P-reflexive eql)) 
              where 
                open import Data.List.Any.Properties
                open Inverse (⊥↔Any⊥ {A = |L₀|} {xs = proj₁ l})

                imp : {l₀ : |L₀|} → {p : |P|} → (x ≈P p) → (p ≈P inj₁ l₀) → const ⊥ l₀
                imp {l₀} {p} x≈p p≈inj₁l₀ with ≈P-trans inj₂r₀≈x (≈P-trans x≈p p≈inj₁l₀)
                imp {l₀} {p} x≈p p≈inj₁l₀ | ()
            eliminator x f inj₂r₀≈x x∈≡a | inj₂ x∈proj₁ar =
                ∈-resp-≈ ≈P-setoid (≈P-sym inj₂r₀≈x) x∈proj₁ar
        --]]]

        r₀∈r : r₀ ∈R r
        r₀∈r = pointwiseRespAny⃖ imp (proj₁ r) (proj₁ ar) inj₂r₀∈ar (LPW.map ≈P-reflexive eqr) 
          where
            imp : {r₀' : |R₀|} → {p : |P|} → (inj₂ r₀ ≈P p) →  (p ≈P inj₂ r₀') → (r₀ ≈R₀ r₀')
            imp {r₀'} {p} inj₂r₀≈p p≈inj₂r₀' with (≈P-trans inj₂r₀≈p p≈inj₂r₀')
            imp {r₀'} {p} inj₂r₀≈p p≈inj₂r₀' | ₂∼₂ r₀≈r₀' = r₀≈r₀'

        r₀∈fRgRr : r₀ ∈R (|fR| $ |gR| r)
        r₀∈fRgRr = E2.from ⟨$⟩ r₀∈r

        module E3 = Equivalence (|f|-prop (|g| a) (inj₂ r₀))

      --]]]

    sameElements : (p : |P|) → (p ∈P a) ⇔ (p ∈P (|f| $ |g| a))
    sameElements p = equivalence (p← p) (p→ p) 
  --]]]

inv-S→FP→S : (a : Carrier') → ((|g| $ |f| a) ≈' a)
--[[[

inv-S→FP→S (aL , aR) with decompose $ |f| (aL , aR)
inv-S→FP→S (aL , aR) | l , r , atl , atr , aeql , aeqr , aconcat =
  eq1 , eq2
  where
    aconcat' : proj₁ (|f| $ aL , aR) ≡ (proj₁ atl ++ proj₁ atr)
    aconcat' = aconcat

    invaux-S→FP→S : (x : |P|) → (x ∈P (|f| $ aL , aR)) ⇔ (P-|f| (aL , aR) x)
    invaux-S→FP→S x = |f|-prop (aL , aR) x

    fLaL≈l : |fL| aL ≈FL l
    fLaL≈l = ≈FL-sym {l} {|fL| aL} (E.from ⟨$⟩ x∈l⇔x∈fLaL)
      where
        module E = Equivalence (c1≈c2⇔sameElementsL l (|fL| aL))  
        p→ : (x : |L₀|) → (x ∈L |fL| aL) → (x ∈L l)
        p→ x x∈fLaL = pointwiseRespAny⃖ imp (proj₁ l) (proj₁ atl) inj₁x∈atl aeql 
          where 
            inj₁x∈fa : (inj₁ x) ∈P |f| (aL , aR)
            inj₁x∈fa = from ⟨$⟩ (inj₁ $ x , ≈P-refl , x∈fLaL)
              where
                open Equivalence (invaux-S→FP→S $ inj₁ x)

            inj₁x∈atl++atr : (inj₁ x) ∈P' ((proj₁ atl) ++ (proj₁ atr))
            inj₁x∈atl++atr rewrite (PE.sym aconcat) = inj₁x∈fa 

            inj₁x∈atl : (inj₁ x) ∈P' (proj₁ atl)
            inj₁x∈atl with ∈-++⁻ ≈P-setoid (proj₁ atl) inj₁x∈atl++atr 
              where
                open import Data.List.Membership.Setoid.Properties
            inj₁x∈atl | inj₁ inj₁x∈atl = inj₁x∈atl
            inj₁x∈atl | inj₂ inj₁x∈atr = 
              ⊥-elim $ (from ⟨$⟩ pointwiseRespAny⃖ imp (proj₁ r) (proj₁ atr) inj₁x∈atr aeqr)  
              where
                open import Data.List.Any.Properties
                open Inverse ⊥↔Any⊥
                imp : {a : |P|} → {b : |R₀|} → (inj₁ x ≈P a) → (a ≡ inj₂ b) → const ⊥ |R₀|
                imp {a} {b} inj₁x≈a a≡inj₂b with ≈P-trans inj₁x≈a (≈P-reflexive a≡inj₂b)
                imp {a} {b} inj₁x≈a a≡inj₂b | (₁∼₂ ())

            imp : ∀ {a : |P|} → {b : |L₀|} → (inj₁ x ≈P a) → (a ≡ inj₁ b) → (x ≈L₀ b)
            imp {a} {b} inj₁x≈a a≡inj₁b with ≈P-trans inj₁x≈a (≈P-reflexive a≡inj₁b)
            imp {a} {b} inj₁x≈a a≡inj₁b | (₁∼₁ x≈b) = x≈b

        p← : (x : |L₀|) → (x ∈L l) → (x ∈L |fL| aL)
        p← x x∈l with to ⟨$⟩ inj₁x∈fa 
          where
            open Equivalence (|f|-prop (aL , aR) (inj₁ x))  
            inj₁x∈atl : (inj₁ x) ∈P' (proj₁ atl)
            inj₁x∈atl = pointwiseRespAny imp (proj₁ l) (proj₁ atl) x∈l aeql 
              where
                imp : ∀ {a b} → (x ≈L₀ a) → (b ≡ inj₁ a) → (inj₁ x ≈P b)
                imp {a} {b} x≈a b≡inj₁a = ≈P-trans (₁∼₁ x≈a) (≈P-reflexive $ PE.sym b≡inj₁a)
            inj₁x∈fa : (inj₁ x) ∈P (|f| $ aL , aR)
            inj₁x∈fa rewrite aconcat = ∈-++⁺ˡ ≈P-setoid inj₁x∈atl 
              where
                open import Data.List.Membership.Setoid.Properties
        p← x x∈l | inj₁ (l₀ , (₁∼₁ x≈l₀) , l₀∈fLaL) =
          LAny.map (λ l₀≈· → ≈L₀-trans x≈l₀ l₀≈·) l₀∈fLaL  
        p← x x∈l | inj₂ (r₀ , (₁∼₂ ()) , r₀∈fRaR)

        x∈l⇔x∈fLaL : (x : |L₀|) → (x ∈L l) ⇔ x ∈L (|fL| aL)
        x∈l⇔x∈fLaL x = equivalence (p← x) (p→ x)

    fRaR≈r : |fR| aR ≈FR r
    fRaR≈r = ≈FR-sym {r} {|fR| aR} (E.from ⟨$⟩ x∈r⇔x∈fRaR)
      where
        module E = Equivalence (c1≈c2⇔sameElementsR r (|fR| aR))  
        p→ : (x : |R₀|) → (x ∈R |fR| aR) → (x ∈R r)
        p→ x x∈fRaR = pointwiseRespAny⃖ imp (proj₁ r) (proj₁ atr) inj₂x∈atr aeqr 
          where 
            inj₂x∈fa : (inj₂ x) ∈P |f| (aL , aR)
            inj₂x∈fa = from ⟨$⟩ (inj₂ $ x , ≈P-refl , x∈fRaR)
              where
                open Equivalence (invaux-S→FP→S $ inj₂ x)

            inj₂x∈atl++atr : (inj₂ x) ∈P' ((proj₁ atl) ++ (proj₁ atr))
            inj₂x∈atl++atr rewrite (PE.sym aconcat) = inj₂x∈fa 

            inj₂x∈atr : (inj₂ x) ∈P' (proj₁ atr)
            inj₂x∈atr with ∈-++⁻ ≈P-setoid (proj₁ atl) inj₂x∈atl++atr 
              where
                open import Data.List.Membership.Setoid.Properties
            inj₂x∈atr | inj₁ inj₂x∈atl = 
              ⊥-elim $ (from ⟨$⟩ pointwiseRespAny⃖ imp (proj₁ l) (proj₁ atl) inj₂x∈atl aeql)  
              where
                open import Data.List.Any.Properties
                open Inverse ⊥↔Any⊥
                imp : {a : |P|} → {b : |L₀|} → (inj₂ x ≈P a) → (a ≡ inj₁ b) → const ⊥ |R₀|
                imp {a} {b} inj₂x≈a a≡inj₂b with ≈P-trans inj₂x≈a (≈P-reflexive a≡inj₂b)
                imp {a} {b} inj₂x≈a a≡inj₂b | ()
            inj₂x∈atr | inj₂ inj₂x∈atr = inj₂x∈atr

            imp : ∀ {a : |P|} → {b : |R₀|} → (inj₂ x ≈P a) → (a ≡ inj₂ b) → (x ≈R₀ b)
            imp {a} {b} inj₂x≈a a≡inj₂b with ≈P-trans inj₂x≈a (≈P-reflexive a≡inj₂b)
            imp {a} {b} inj₂x≈a a≡inj₂b | (₂∼₂ x≈b) = x≈b

        p← : (x : |R₀|) → (x ∈R r) → (x ∈R |fR| aR)
        p← x x∈r with to ⟨$⟩ inj₂x∈fa 
          where
            open Equivalence (|f|-prop (aL , aR) (inj₂ x))  
            inj₂x∈atr : (inj₂ x) ∈P' (proj₁ atr)
            inj₂x∈atr = pointwiseRespAny imp (proj₁ r) (proj₁ atr) x∈r aeqr 
              where
                imp : ∀ {a b} → (x ≈R₀ a) → (b ≡ inj₂ a) → (inj₂ x ≈P b)
                imp {a} {b} x≈a b≡inj₂a = ≈P-trans (₂∼₂ x≈a) (≈P-reflexive $ PE.sym b≡inj₂a)
            inj₂x∈fa : (inj₂ x) ∈P (|f| $ aL , aR)
            inj₂x∈fa rewrite aconcat = ∈-++⁺ʳ ≈P-setoid (proj₁ atl) inj₂x∈atr 
              where
                open import Data.List.Membership.Setoid.Properties
        p← x x∈l | inj₁ (l₀ , () , l₀∈fLaL)
        p← x x∈l | inj₂ (r₀ , (₂∼₂ x≈r₀) , r₀∈fRaR) =
          LAny.map (λ r₀≈· → ≈R₀-trans x≈r₀ r₀≈·) r₀∈fRaR  

        x∈r⇔x∈fRaR : (x : |R₀|) → (x ∈R r) ⇔ x ∈R (|fR| aR)
        x∈r⇔x∈fRaR x = equivalence (p← x) (p→ x)

    eq1 : |gL| l ≈L aL
    eq1 = 
      begin
        |gL| l ≈⟨ |gL|-≈ l (|fL| aL) (≈FL-sym {|fL| aL} {l} fLaL≈l) ⟩
        |gL| (|fL| aL) ≈⟨ L-inv-S→FP→S aL ⟩
        aL
       ∎
      where
        open import Relation.Binary.EqReasoning ≈L-setoid

    eq2 : |gR| r ≈R aR
    eq2 = 
      begin
        |gR| r ≈⟨ |gR|-≈ r (|fR| aR) (≈FR-sym {|fR| aR} {r} fRaR≈r) ⟩
        |gR| (|fR| aR) ≈⟨ R-inv-S→FP→S aR ⟩
        aR
       ∎
      where
        open import Relation.Binary.EqReasoning ≈R-setoid

--]]]


sem : SemSemilatIso l0 l0 l0 l0 l0 l0 l0 (ProductSemilat isSemilatL isSemilatR)
sem = record
  { f = |f| , |f|-≈ , |f|-⊥ , |f|-∨
  ; g = |g| , |g|-≈ , |g|-⊥ , |g|-∨
  ; inv-S→FP→S = inv-S→FP→S
  ; inv-FP→S→FP = inv-FP→S→FP
  }
