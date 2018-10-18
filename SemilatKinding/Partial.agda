open import SemKinding
open import SemilatKinding.Core
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import RelationalStructures
open import Util
open import Syntax using (τ)
open import Kinding using (IsSemilat)
open import Function using (_$_)
open import Relation.Binary.Lattice
open import Kinding
open import FreeForgetfulAdjunction
open import Data.Sum
open import Data.Sum.Relation.Pointwise
open import Data.Product
open import Data.List
open import Data.List.Relation.Pointwise as LPW
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
open import Data.List.All as LAll
open import Data.List.Any as LAny
open import Data.Unit 
open import Data.Empty
open import Function.Equivalence
open import Function.Equality

module SemilatKinding.Partial 
  {τContent τContent₀ : τ} 
  {isSemilatContent : IsSemilat τContent τContent₀} 
  (semSemilatContent : SemSemilatIso l0 l0 l0 l0 l0 l0 l0 isSemilatContent)
 where

S : BoundedJoinSemilattice l0 l0 l0
S = SemSemilatCore.S ⟦ PartialSemilat isSemilatContent ⁂⟧

|S| : Set
|S| = BoundedJoinSemilattice.Carrier S

P : DeltaPoset {l0} {l0} {l0} {l0}
P = SemSemilatCore.P ⟦ PartialSemilat isSemilatContent ⁂⟧ 

open import FreeSemilattice P as FP hiding (⊥)

|P| : Set
|P| = DeltaPoset.Carrier P

S₀ : BoundedJoinSemilattice l0 l0 l0
S₀ = SemSemilatCore.S ⟦ isSemilatContent ⁂⟧

|S₀| : Set
|S₀| = BoundedJoinSemilattice.Carrier S₀

P₀ : DeltaPoset {l0} {l0} {l0} {l0}
P₀ = SemSemilatCore.P ⟦ isSemilatContent ⁂⟧

import FreeSemilattice P₀ as FP₀

|P₀| : Set
|P₀| = DeltaPoset.Carrier P₀

_≈S_ = BoundedJoinSemilattice._≈_ S
≈S-refl = BoundedJoinSemilattice.refl S
≈S-setoid : Setoid _ _
≈S-setoid = record
  { Carrier = |S|
  ; isEquivalence = BoundedJoinSemilattice.isEquivalence S
  }
_≈S₀_ = BoundedJoinSemilattice._≈_ S₀
≈S₀-setoid : Setoid _ _
≈S₀-setoid = record
  { Carrier = |S₀|
  ; isEquivalence = BoundedJoinSemilattice.isEquivalence S₀
  }
_∨S_ = BoundedJoinSemilattice._∨_ S
_∨S₀_ = BoundedJoinSemilattice._∨_ S₀
⊥S = BoundedJoinSemilattice.⊥ S
⊥S₀ = BoundedJoinSemilattice.⊥ S₀
_≈FP_ = BoundedJoinSemilattice._≈_ (FP P)
≈FP-refl = FP.≈-refl
≈FP-reflexive = FP.≈-reflexive
_∨FP_ = BoundedJoinSemilattice._∨_ (FP P)
⊥FP = BoundedJoinSemilattice.⊥ (FP P)
_≈FP₀_ = BoundedJoinSemilattice._≈_ (FP P₀) 
≈FP₀-sym = FP₀.≈-sym
_∨FP₀_ = BoundedJoinSemilattice._∨_ (FP P₀)
⊥FP₀ = BoundedJoinSemilattice.⊥ (FP P₀)

_≈P_ = DeltaPoset._≈_ P 
≈P-setoid = DeltaPoset.≈-setoid P
≈P-reflexive = DeltaPoset.reflexive≈ P
≈P-refl = DeltaPoset.reflexive≈ P
≈P-sym = DeltaPoset.sym≈ P
≈P-trans = DeltaPoset.trans≈ P
_≈P₀_ = DeltaPoset._≈_ P₀
≈P₀-sym = DeltaPoset.sym≈ P₀
≈P₀-reflexive = DeltaPoset.reflexive≈ P₀
≈P₀-refl = DeltaPoset.refl≈ P₀
≈P₀-trans = DeltaPoset.trans≈ P₀
≈P₀-setoid = DeltaPoset.≈-setoid P₀
_<P₀_ = DeltaPoset._<_ P₀
_<P_ = DeltaPoset._<_ P
_⊑P_ = DeltaPoset._⊑_ P
⊑P-trans = DeltaPoset.trans⊑ P
⊑P-refl = DeltaPoset.refl⊑ P
⊑P-reflexive = DeltaPoset.reflexive⊑ P
_⊑P₀_ = DeltaPoset._⊑_ P₀
⊑P₀-trans = DeltaPoset.trans⊑ P₀
⊑P₀-refl = DeltaPoset.refl⊑ P₀
⊑P₀-reflexive = DeltaPoset.reflexive⊑ P₀
⊑P₀-respʳ-≈P₀ = DeltaPoset.⊑-respʳ-≈ P₀
⊑P₀-respˡ-≈P₀ = DeltaPoset.⊑-respˡ-≈ P₀
_∦P_ = DeltaPoset._∦_ P
_∦P₀_ = DeltaPoset._∦_ P₀
_∈P_ = FP._∈_
_∈P₀_ = FP₀._∈_

|f₀| : (BoundedJoinSemilattice.Carrier S₀) → (BoundedJoinSemilattice.Carrier $ FP P₀)
|f₀| = proj₁ $ SemSemilatIso.f semSemilatContent

|f₀|-≈ : (a b : BoundedJoinSemilattice.Carrier S₀) → a ≈S₀ b → (|f₀| a) ≈FP₀ (|f₀| b)
|f₀|-≈ = proj₁ $ proj₂ $ SemSemilatIso.f semSemilatContent

|f₀|-⊥ : (|f₀| $ BoundedJoinSemilattice.⊥ S₀) ≈FP₀ (BoundedJoinSemilattice.⊥ $ FP P₀) 
|f₀|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilatIso.f semSemilatContent

|f₀|-∨ : (a b : BoundedJoinSemilattice.Carrier S₀) → (|f₀| $ a ∨S₀ b) ≈FP₀ ((|f₀| a) ∨FP₀ (|f₀| b))
|f₀|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilatIso.f semSemilatContent 

--TODO: this was pasted from product kinding... maybe it should be moved into a "Utils" module?
convL : (z : List |P₀|) → (f : FP₀.IsFreeList z) → 
        Σ[ l ∈ FP.SemilatCarrier ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) z (proj₁ l))
--[[[
convL [] []-Free = ([] , []-Free) , []
convL (h ∷ t) (∷-Free h t min incomp ft) = 
  ((inj₁ h) ∷ t' , ∷-Free (inj₁ h) t' min' incomp₀ ft') , (PE.refl ∷ eqt')
  where
    imp1 : ∀ {a : |P₀|} → {b : |P|} → (h <P₀ a) → (b ≡ inj₁ a) → (inj₁ h <P b)
    imp1 {a} {b} h<a b≡injA@PE.refl = ₁∼₁ h<a  

    r : Σ[ l ∈ FP.SemilatCarrier ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) t (proj₁ l))
    r = convL t ft

    t' : List |P|
    t' = proj₁ $ proj₁ r

    ft' : IsFreeList t'
    ft' = proj₂ $ proj₁ r

    eqt' : LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) t t'
    eqt' = proj₂ r

    min' : All (λ z → inj₁ h <P z) t'
    min' = pointwiseRespAll imp1 t t' min eqt'

    ⊑-resp-inj₁ : {a b : |P₀|} → inj₁ a ⊑P inj₁ b → a ⊑P₀ b
    ⊑-resp-inj₁ {a} {b} (₁∼₁ a⊑b) = a⊑b

    p : {a : |P|} → {b : |P₀|} → a ∈≡ t' → (a ≡ inj₁ b) → b ∈≡ t
    p {a} {b} a∈≡t' a≡injb = pointwiseRespAny imp t' t a∈≡t' (LPW.symmetric PE.sym eqt')  
      where
        open import Data.Sum.Properties
        imp : ∀ {x : |P|} → {y : |P₀|} → (a ≡ x) → (inj₁ y ≡ x) → (b ≡ y) 
        imp {x} {y} PE.refl PE.refl = inj₁-injective (PE.sym a≡injb) 

    ¬inj₂tt∈≡t' : ¬ ((inj₂ tt) ∈≡ t')
    ¬inj₂tt∈≡t' inj₂tt∈≡t' = from ⟨$⟩ pointwiseRespAny imp t' t inj₂tt∈≡t' (LPW.symmetric PE.sym eqt')  
      where
        open import Data.Sum.Properties
        open import Data.List.Any.Properties using (⊥↔Any⊥)
        open import Function.Inverse using (Inverse)
        open import Function.Equality using (_⟨$⟩_)

        open Inverse ⊥↔Any⊥
        imp : ∀ {x : |P|} → {y : |P₀|} → (inj₂ tt ≡ x) → (inj₁ y ≡ x) → ⊥ 
        imp {x} {y} PE.refl () 
      
    incomp₀ : ¬ Any (λ z → inj₁ h ∦P z) t'
    incomp₀ injh∦t' = anyEliminate t' eliminator injh∦t'
      where
        eliminator : AnyEliminator {ℓQ = l0} |P| ⊥ (inj₁ h ∦P_) t'
        eliminator (inj₁ a₀) f (inj₂ injh⊑inja₀) inja₀∈≡t' = incomp $ LAny.map (λ a₀≡· → PE.subst (h ∦P₀_) a₀≡· h∦a₀) (p inja₀∈≡t' PE.refl)    
          where
            h∦a₀ : h ∦P₀ a₀
            h∦a₀ = inj₂ (⊑-resp-inj₁ injh⊑inja₀)
        eliminator (inj₁ a₀) f (inj₁ inja₀⊑injh) inja₀∈≡t' = incomp $ LAny.map (λ a₀≡· → PE.subst (h ∦P₀_) a₀≡· h∦a₀) (p inja₀∈≡t' PE.refl)    
          where
            h∦a₀ : h ∦P₀ a₀
            h∦a₀ = inj₁ (⊑-resp-inj₁ inja₀⊑injh)

        eliminator (inj₂ tt) f (inj₁ (₁∼₂ tt)) injtt∈≡t' = ¬inj₂tt∈≡t' injtt∈≡t' 
        eliminator (inj₂ a₀) f (inj₂ ()) inja₀∈≡t'
--]]]

P-|f| : (a : |S|) → (x : |P|) → Set
P-|f| (inj₁ a₀) x = Σ[ y ∈ |P₀| ] (x ≈P inj₁ y) × (y FP₀.∈ |f₀| a₀)
P-|f| (inj₂ tt) x = x ≈P inj₂ tt

|f|-aux : (a : |S|) → Σ[ c ∈ FP.SemilatCarrier ] ∀ (x : |P|) → x ∈P c ⇔ P-|f| a x 
--[[[

|f|-aux (inj₁ a₀) = proj₁ res , res-prop⇔
  --[[[

  where
    factored : Σ[ l ∈ List |P₀| ] (FP₀.IsFreeList l)
    factored = |f₀| a₀

    res : Σ[ l ∈ FP.SemilatCarrier ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) (proj₁ factored) (proj₁ l))
    res = convL (proj₁ factored) (proj₂ factored)

    res-list : List |P|
    res-list = proj₁ $ proj₁ res

    res-free : IsFreeList res-list
    res-free = proj₂ $ proj₁ res

    res-eq : (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) (proj₁ factored) res-list)
    res-eq = proj₂ res

    res-prop← : ∀ (x : |P|) → Σ[ y ∈ |P₀| ] (x ≈P inj₁ y) × (y FP₀.∈ |f₀| a₀) → (x FP.∈ (proj₁ res))
    res-prop← x (y , x-≈P-inj₁y , y-∈FP₀~f₀a₀) = p₀'
      where
        open import Data.List.Membership.Setoid.Properties
        imp : ∀ {a : |P|} → {b : |P₀|} → (y ≈P₀ b) → (a ≡ inj₁ b) → (a ≈P inj₁ y)
        imp {a} {b} y-≈L₀-b a-≡-inj₁b = DeltaPoset.Eq.trans P a-≈P-inj₁b (₁∼₁ (≈P₀-sym y-≈L₀-b))  
          where
            open Setoid ≈P-setoid

            a-≈P-inj₁b : a ≈P inj₁ b
            a-≈P-inj₁b = ≈P-reflexive a-≡-inj₁b

        p : Any (λ · → · ≈P inj₁ y) res-list
        p = pointwiseRespAny imp (proj₁ $ |f₀| a₀) res-list y-∈FP₀~f₀a₀ res-eq 

        p₀ : inj₁ y FP.∈ proj₁ res
        p₀ = LAny.map (λ ·-≈P-inj₁y → DeltaPoset.Eq.sym P ·-≈P-inj₁y) p

        p₀' : x FP.∈ proj₁ res
        p₀' = LAny.map (λ inj₁y-≈P-· → DeltaPoset.Eq.trans P x-≈P-inj₁y inj₁y-≈P-·) p₀

    res-prop→ : ∀ (x : |P|) → x ∈P (proj₁ res) → Σ[ y ∈ |P₀| ] (x ≈P inj₁ y) × (y FP₀.∈ |f₀| a₀)
    res-prop→ x x∈res = anyEliminate (proj₁ $ |f₀| a₀) elim p
      where
        imp : ∀ {a : |P|} → {b : |P₀|} → (x ≈P a) → (a ≡ inj₁ b) → (x ≈P inj₁ b)
        imp {a} {b} x≈a a≡inj₁b = PE.subst (λ · → x ≈P ·) a≡inj₁b x≈a 

        p : Any (λ · → x ≈P inj₁ ·) (proj₁ $ |f₀| a₀)
        p = pointwiseRespAny⃖ imp (proj₁ $ |f₀| a₀) res-list x∈res res-eq

        elim : AnyEliminator {ℓQ = l0} |P₀| (Σ[ y ∈ |P₀| ] (x ≈P inj₁ y) × (y FP₀.∈ |f₀| a₀)) (λ · → x ≈P inj₁ ·) (proj₁ $ |f₀| a₀) 
        elim a f x≈Pa a∈≡fLaL = (a , x≈Pa , LAny.map (λ a∈≡· → ≈P₀-reflexive a∈≡·) a∈≡fLaL)

    res-prop⇔ : (x : |P|) → (x ∈P proj₁ res) ⇔ P-|f| (inj₁ a₀) x
    res-prop⇔ x = equivalence (res-prop→ x) (res-prop← x)

  --]]]
|f|-aux (inj₂ tt) = (c , p)
  --[[[ 
  where
    c = (inj₂ tt ∷ []) , (∷-Free (inj₂ tt) [] [] (λ ()) []-Free)
    p : ∀ (x : |P|) → x ∈P c ⇔ P-|f| (inj₂ tt) x
    --[[[
    p x = equivalence p→ p←
      where
        p→ : x ∈P c → P-|f| (inj₂ tt) x
        p→ (here x≈inj₂tt) = x≈inj₂tt
        p→ (there x∈[]) = ⊥-elim $ ¬Any[] x∈[]
          where
            open import Data.List.Any.Properties using (¬Any[])
       
        p← : P-|f| (inj₂ tt) x → x ∈P c
        p← x≈inj₂tt = here x≈inj₂tt 
    --]]]
  --]]]

--]]]


|f| : (BoundedJoinSemilattice.Carrier S) → (BoundedJoinSemilattice.Carrier $ FP P)
|f| c = proj₁ $ |f|-aux c

|f|-prop : (c : |S|) → (x : |P|) → (x ∈P (|f| c)) ⇔ (P-|f| c x)
|f|-prop c = proj₂ $ |f|-aux c

f-≈ : (a b : |S|) → a ≈S b → (|f| a) ≈FP (|f| b)
--[[[
f-≈ (inj₁ a₀) (inj₂ tt) (₁∼₂ ())
f-≈ (inj₁ a₀) (inj₁ b₀) (₁∼₁ a₀≈b₀) = from ⟨$⟩ sameElements 
  where
    p→ : (p : |P|) → p ∈P (|f| $ inj₁ a₀) → p ∈P (|f| $ inj₁ b₀)
    --[[[
    p→ p p∈|f|-inj₁a₀ with to ⟨$⟩ p∈|f|-inj₁a₀ 
      where
        open Equivalence (|f|-prop (inj₁ a₀) p)
    p→ p p∈|f|-inj₁a₀ | (p₀ , p≈inj₁p₀ , p₀∈f₀a₀) = 
      E3.from ⟨$⟩ (p₀ , p≈inj₁p₀ , p₀∈f₀b₀) 
      where
        open import Data.List.Membership.Setoid.Properties
        module E1 = Equivalence (FP₀.c1≈c2⇔sameElements (|f₀| a₀) (|f₀| b₀))
        module E2 = Equivalence ((E1.to ⟨$⟩ |f₀|-≈ a₀ b₀ a₀≈b₀) p₀)

        p₀∈f₀b₀ : p₀ FP₀.∈ (|f₀| b₀)
        p₀∈f₀b₀ = E2.to ⟨$⟩ p₀∈f₀a₀

        module E3 = Equivalence (|f|-prop (inj₁ b₀) p)
    --]]]

    p← : (p : |P|) → (p ∈P (|f| $ inj₁ b₀) → (p ∈P (|f| $ inj₁ a₀)))
    --[[[
    p← p p∈|f|-inj₁b₀ with to ⟨$⟩ p∈|f|-inj₁b₀
      where
        open Equivalence (|f|-prop (inj₁ b₀) p)
    p← p p∈fc2 | (p₀ , p≈inj₁p₀ , p₀∈f₀b₀) = 
      E3.from ⟨$⟩ (p₀ , p≈inj₁p₀ , p₀∈f₀a₀) 
      where
        open import Data.List.Membership.Setoid.Properties
        module E1 = Equivalence (FP₀.c1≈c2⇔sameElements (|f₀| a₀) (|f₀| b₀))
        module E2 = Equivalence ((E1.to ⟨$⟩ |f₀|-≈ a₀ b₀ a₀≈b₀) p₀)

        p₀∈f₀a₀ : p₀ FP₀.∈ (|f₀| a₀)
        p₀∈f₀a₀ = E2.from ⟨$⟩ p₀∈f₀b₀

        module E3 = Equivalence (|f|-prop (inj₁ a₀) p)
    --]]]
  
    sameElements : (p : |P|) → (p ∈P (|f| $ inj₁ a₀)) ⇔ (p ∈P (|f| $ inj₁ b₀))
    sameElements p = equivalence (p→ p) (p← p) 

    open Equivalence (FP.c1≈c2⇔sameElements (|f| $ inj₁ a₀) (|f| $ inj₁ b₀)) 
f-≈ (inj₂ tt) (inj₂ tt) (₂∼₂ PE.refl) = ≈FP-refl {|f| $ inj₂ tt}
--]]]

f-⊥ : |f| ⊥S ≈FP ⊥FP
--[[[
f-⊥ = from ⟨$⟩ sameElements
  where
    p→ : (p : |P|) → p ∈P (|f| ⊥S) → p ∈P ⊥FP
    p→ p p∈f⊥ with to ⟨$⟩ p∈f⊥
      where
        open Equivalence (|f|-prop ⊥S p)
    p→ p p∈f⊥ | (p₀ , p≈inj₁p₀ , p₀∈f₀⊥S₀) = ⊥-elim $ ¬Any[] p₀∈⊥FP₀ 
      where
        open import Data.List.Any.Properties
        p₀∈⊥FP₀ : p₀ FP₀.∈ ⊥FP₀
        p₀∈⊥FP₀ = FP₀.p∈c1≈c2 {p₀} {|f₀| ⊥S₀} {⊥FP₀} |f₀|-⊥ p₀∈f₀⊥S₀

    p← : (p : |P|) → p ∈P ⊥FP → p ∈P (|f| ⊥S)
    p← p p∈⊥FP = ⊥-elim $ ¬Any[] p∈⊥FP
      where
        open import Data.List.Any.Properties using (¬Any[])

    sameElements : (p : |P|) → (p ∈P (|f| ⊥S)) ⇔ (p ∈P ⊥FP)
    sameElements p = equivalence (p→ p) (p← p)

    open Equivalence (FP.c1≈c2⇔sameElements (|f| ⊥S) ⊥FP)
--]]]

f-∨ : (a b : |S|) → (|f| $ a ∨S b) ≈FP ((|f| a) ∨FP (|f| b))
--[[[
f-∨ a@(inj₁ a₀) b@(inj₁ b₀) =
  from ⟨$⟩ sameElements
  where
    p→ : (p : |P|) → p ∈P (|f| $ a ∨S b) → p ∈P ((|f| a) ∨FP (|f| b))
    --[[[
    p→ p p∈|f|-a∨b with to ⟨$⟩ p∈|f|-a∨b
      where
        open Equivalence (|f|-prop (a ∨S b) p)
    p→ p p∈|f|-a∨b | (p₀ , p≈inj₁p₀ , p₀∈|f₀|-a₀∨b₀) with to ⟨$⟩ p₀∈|f₀|a-∨-|f₀|b
      where
        p₀∈|f₀|a-∨-|f₀|b : p₀ FP₀.∈ ((|f₀| a₀) FP₀.∨ (|f₀| b₀))
        p₀∈|f₀|a-∨-|f₀|b = 
          (FP₀.p∈c1≈c2 {p₀} {|f₀| (a₀ ∨S₀ b₀)} {(|f₀| a₀) FP₀.∨ (|f₀| b₀)} $ |f₀|-∨ a₀ b₀) p₀∈|f₀|-a₀∨b₀

        open Equivalence (FP₀.x∈∨⇔P∨ 
          (|f₀| a₀) (|f₀| b₀) ((|f₀| a₀) FP₀.∨ (|f₀| b₀)) 
          (FP₀.≈-refl {(|f₀| a₀) FP₀.∨ (|f₀| b₀)}) p₀)
    p→ p@(inj₁ p₀) p∈|f|-a∨b | (p₀' , p≈inj₁p₀'@(₁∼₁ p₀≈p₀') , p₀'∈|f₀|-a₀∨b₀) | inj₁ (p₀'∈|f₀|a₀ , ¬p₀'⊑|f₀|b₀) = 
      from ⟨$⟩ inj₁ (p∈|f|a , ¬p⊑|f|b) 
      where
        p∈|f|a : p ∈P (|f| a)
        p∈|f|a = from ⟨$⟩ (p₀' , p≈inj₁p₀' , p₀'∈|f₀|a₀)
          where
            open Equivalence (|f|-prop a p)

        ¬p⊑|f|b : ¬ (Any (p ⊑P_) (proj₁ $ |f| b))
        ¬p⊑|f|b p⊑|f|b = anyEliminate (proj₁ $ |f| b) elim p⊑|f|b
          where
            elim : AnyEliminator {ℓQ = l0} |P| ⊥ (p ⊑P_) (proj₁ $ |f| b)
            elim (inj₁ x') f (₁∼₁ p₀≈x') inj₁x'∈|f|b with to ⟨$⟩ (LAny.map ≈P-refl inj₁x'∈|f|b)
              where
                open Equivalence (|f|-prop b (inj₁ x'))
            elim (inj₁ x') f (₁∼₁ p₀⊑x') inj₁x∈|f|b | (z' , ₁∼₁ x'≈z' , z'∈|f₀|b₀) = 
              ¬p₀'⊑|f₀|b₀ $ LAny.map (⊑P₀-respˡ-≈P₀ p₀≈p₀') p₀⊑|f₀|b₀
              where
                z'⊑|f₀|b₀ : Any (z' ⊑P₀_) (proj₁ $ |f₀| b₀)
                z'⊑|f₀|b₀ = LAny.map ⊑P₀-reflexive z'∈|f₀|b₀

                p₀⊑|f₀|b₀ : Any (p₀ ⊑P₀_) (proj₁ $ |f₀| b₀)
                p₀⊑|f₀|b₀ = LAny.map (λ z'⊑· → ⊑P₀-trans (⊑P₀-trans p₀⊑x' (⊑P₀-reflexive x'≈z')) z'⊑·) z'⊑|f₀|b₀
            elim (inj₂ tt) f (₁∼₂ tt) inj₂tt∈|f|b with to ⟨$⟩ (LAny.map ≈P-refl inj₂tt∈|f|b)
              where
                open Equivalence (|f|-prop b (inj₂ tt)) 
            elim (inj₂ tt) f (₁∼₂ tt) inj₂tt∈|f|b | ()
        
        open Equivalence (FP.x∈∨⇔P∨ (|f| a) (|f| b) ((|f| a) FP.∨ (|f| b)) (FP.≈-refl {(|f| a) FP.∨ (|f| b)}) p)
    p→ p@(inj₁ p₀) p∈|f|-a∨b | (p₀' , p≈inj₁p₀'@(₁∼₁ p₀≈p₀') , p₀'∈|f₀|-a₀∨b₀) | inj₂ (inj₁ (p₀'∈|f₀|b₀ , ¬p₀'⊑|f₀|a₀)) =
      from ⟨$⟩ inj₂ (inj₁ (p∈|f|b , ¬p⊑|f|a)) 
      where
        p∈|f|b : p ∈P (|f| b)
        p∈|f|b = from ⟨$⟩ (p₀' , p≈inj₁p₀' , p₀'∈|f₀|b₀)
          where
            open Equivalence (|f|-prop b p)

        ¬p⊑|f|a : ¬ (Any (p ⊑P_) (proj₁ $ |f| a))
        ¬p⊑|f|a p⊑|f|a = anyEliminate (proj₁ $ |f| a) elim p⊑|f|a
          where
            elim : AnyEliminator {ℓQ = l0} |P| ⊥ (p ⊑P_) (proj₁ $ |f| a)
            elim (inj₁ x') f (₁∼₁ p₀≈x') inj₁x'∈|f|a with to ⟨$⟩ (LAny.map ≈P-refl inj₁x'∈|f|a)
              where
                open Equivalence (|f|-prop a (inj₁ x'))
            elim (inj₁ x') f (₁∼₁ p₀⊑x') inj₁x∈|f|a | (z' , ₁∼₁ x'≈z' , z'∈|f₀|a₀) = 
              ¬p₀'⊑|f₀|a₀ $ LAny.map (⊑P₀-respˡ-≈P₀ p₀≈p₀') p₀⊑|f₀|a₀
              where
                z'⊑|f₀|a₀ : Any (z' ⊑P₀_) (proj₁ $ |f₀| a₀)
                z'⊑|f₀|a₀ = LAny.map ⊑P₀-reflexive z'∈|f₀|a₀

                p₀⊑|f₀|a₀ : Any (p₀ ⊑P₀_) (proj₁ $ |f₀| a₀)
                p₀⊑|f₀|a₀ = LAny.map (λ z'⊑· → ⊑P₀-trans (⊑P₀-trans p₀⊑x' (⊑P₀-reflexive x'≈z')) z'⊑·) z'⊑|f₀|a₀
            elim (inj₂ tt) f (₁∼₂ tt) inj₂tt∈|f|a with to ⟨$⟩ (LAny.map ≈P-refl inj₂tt∈|f|a)
              where
                open Equivalence (|f|-prop a (inj₂ tt)) 
            elim (inj₂ tt) f (₁∼₂ tt) inj₂tt∈|f|a | ()
        
        open Equivalence (FP.x∈∨⇔P∨ (|f| a) (|f| b) ((|f| a) FP.∨ (|f| b)) (FP.≈-refl {(|f| a) FP.∨ (|f| b)}) p)
      
    p→ p p∈|f|-a∨b | (p₀' , p≈inj₁p₀'@(₁∼₁ p₀≈p₀') , p₀'∈|f₀|-a₀∨b₀) | inj₂ (inj₂ (p₀'∈|f₀|a₀ , p₀'∈|f₀|b₀)) = 
      from ⟨$⟩ inj₂ (inj₂ (p∈|f|a , p∈|f|b)) 
      where
        p∈|f|a : p ∈P (|f| a)
        p∈|f|a = from ⟨$⟩ (p₀' , p≈inj₁p₀' , p₀'∈|f₀|a₀)
          where
            open Equivalence (|f|-prop a p)

        p∈|f|b : p ∈P (|f| b)
        p∈|f|b = from ⟨$⟩ (p₀' , p≈inj₁p₀' , p₀'∈|f₀|b₀)
          where
            open Equivalence (|f|-prop b p)

        open Equivalence (FP.x∈∨⇔P∨ (|f| a) (|f| b) ((|f| a) FP.∨ (|f| b)) (FP.≈-refl {(|f| a) FP.∨ (|f| b)}) p)
    --]]]

    p← : (p : |P|) → p ∈P ((|f| a) ∨FP (|f| b)) → p ∈P (|f| $ a ∨S b)
    --[[[
    p← p p∈|f|a∨|f|b with to ⟨$⟩ p∈|f|a∨|f|b
      where
        open Equivalence (FP.x∈∨⇔P∨ (|f| a) (|f| b) ((|f| a) FP.∨ (|f| b)) (FP.≈-refl {(|f| a) FP.∨ (|f| b)}) p)
    p← p p∈|f|a∨|f|b | inj₁ (p∈|f|a , ¬p⊑|f|b) with to ⟨$⟩ p∈|f|a 
      where 
        open Equivalence (|f|-prop a p)
    p← p@(inj₁ p₀) p∈|f|a∨|f|b | inj₁ (p∈|f|a , ¬p⊑|f|b) | (p₀' , p≈inj₁p₀'@(₁∼₁ p₀≈p₀') , p₀'∈|f₀|a₀) =
      from ⟨$⟩ (p₀ , ₁∼₁ ≈P₀-refl , p₀∈|f₀|a₀∨b₀)
      where
        open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)

        p₀∈|f₀|a₀∨|f₀|b₀ : p₀ ∈P₀ ((|f₀| a₀) ∨FP₀ (|f₀| b₀))
        --[[[
        p₀∈|f₀|a₀∨|f₀|b₀ = from ⟨$⟩ (inj₁ $ (∈-resp-≈ ≈P₀-setoid (≈P₀-sym p₀≈p₀') p₀'∈|f₀|a₀) , ¬p₀⊑|f₀|b₀)  
          where
            open Equivalence (FP₀.x∈∨⇔P∨ (|f₀| a₀) (|f₀| b₀) ((|f₀| a₀) ∨FP₀ (|f₀| b₀)) (LPW.refl ≈P₀-refl) p₀)

            ¬p₀⊑|f₀|b₀ : ¬ Any (p₀ ⊑P₀_) (proj₁ $ |f₀| b₀)
            ¬p₀⊑|f₀|b₀ p₀⊑f₀b₀ = anyEliminate (proj₁ $ |f₀| b₀) elim p₀⊑f₀b₀
              where
                elim : AnyEliminator {ℓQ = l0} |P₀| ⊥ (p₀ ⊑P₀_) (proj₁ $ |f₀| b₀)
                elim x f p₀⊑x x∈f₀b₀ = 
                  ⊥-elim $ ¬p⊑|f|b (LAny.map (λ inj₁x≈· → ⊑P-trans p⊑inj₁x (⊑P-reflexive inj₁x≈·)) inj₁x∈fb) 
                  where
                    module EFB = Equivalence (|f|-prop b (inj₁ x))
                    
                    inj₁x∈fb : (inj₁ x) ∈P (|f| b)
                    inj₁x∈fb = EFB.from ⟨$⟩ (x , ₁∼₁ ≈P₀-refl , (LAny.map ≈P₀-reflexive x∈f₀b₀))

                    p⊑inj₁x : p ⊑P (inj₁ x)
                    p⊑inj₁x = ₁∼₁ p₀⊑x
        --]]]

        p₀∈|f₀|a₀∨b₀ : p₀ ∈P₀ (|f₀| $ a₀ ∨S₀ b₀)
        --[[[
        p₀∈|f₀|a₀∨b₀ = 
          FP₀.p∈c1≈c2 {p₀} {(|f₀| a₀) ∨FP₀ (|f₀| b₀)} {|f₀| $ a₀ ∨S₀ b₀} 
                       (≈FP₀-sym {|f₀| $ a₀ ∨S₀ b₀} {(|f₀| a₀) ∨FP₀ (|f₀| b₀)} (|f₀|-∨ a₀ b₀)) p₀∈|f₀|a₀∨|f₀|b₀ 
        --]]]

        open Equivalence (|f|-prop (a ∨S b) (inj₁ p₀))

    p← p p∈|f|a∨|f|b | inj₂ (inj₁ (p∈|f|b , ¬p⊑|f|a)) with to ⟨$⟩ p∈|f|b 
      where
        open Equivalence (|f|-prop b p)
    p← p@(inj₁ p₀) p∈|f|a∨|f|b | inj₂ (inj₁ (p∈|f|b , ¬p⊑|f|a)) | (p₀' , p≈inj₁p₀'@(₁∼₁ p₀≈p₀') , p₀'∈|f₀|b₀) =
      from ⟨$⟩ (p₀ , ₁∼₁ ≈P₀-refl , p₀∈|f₀|a₀∨b₀)
      where
        open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)

        p₀∈|f₀|a₀∨|f₀|b₀ : p₀ ∈P₀ ((|f₀| a₀) ∨FP₀ (|f₀| b₀))
        --[[[
        p₀∈|f₀|a₀∨|f₀|b₀ = from ⟨$⟩ (inj₂ $ inj₁ $ (∈-resp-≈ ≈P₀-setoid (≈P₀-sym p₀≈p₀') p₀'∈|f₀|b₀) , ¬p₀⊑|f₀|a₀)
          where
            open Equivalence (FP₀.x∈∨⇔P∨ (|f₀| a₀) (|f₀| b₀) ((|f₀| a₀) ∨FP₀ (|f₀| b₀)) (LPW.refl ≈P₀-refl) p₀)

            ¬p₀⊑|f₀|a₀ : ¬ Any (p₀ ⊑P₀_) (proj₁ $ |f₀| a₀)
            ¬p₀⊑|f₀|a₀ p₀⊑f₀a₀ = anyEliminate (proj₁ $ |f₀| a₀) elim p₀⊑f₀a₀
              where
                elim : AnyEliminator {ℓQ = l0} |P₀| ⊥ (p₀ ⊑P₀_) (proj₁ $ |f₀| a₀)
                elim x f p₀⊑x x∈f₀a₀ = 
                  ⊥-elim $ ¬p⊑|f|a (LAny.map (λ inj₁x≈· → ⊑P-trans p⊑inj₁x (⊑P-reflexive inj₁x≈·)) inj₁x∈fa) 
                  where
                    module EFA = Equivalence (|f|-prop a (inj₁ x))
                    
                    inj₁x∈fa : (inj₁ x) ∈P (|f| a)
                    inj₁x∈fa = EFA.from ⟨$⟩ (x , (₁∼₁ ≈P₀-refl) , (LAny.map ≈P₀-reflexive x∈f₀a₀))

                    p⊑inj₁x : p ⊑P (inj₁ x)
                    p⊑inj₁x = ₁∼₁ p₀⊑x
        --]]]

        p₀∈|f₀|a₀∨b₀ : p₀ ∈P₀ (|f₀| $ a₀ ∨S₀ b₀)
        --[[[
        p₀∈|f₀|a₀∨b₀ = 
          FP₀.p∈c1≈c2 {p₀} {(|f₀| a₀) ∨FP₀ (|f₀| b₀)} {|f₀| $ a₀ ∨S₀ b₀} 
                       (≈FP₀-sym {|f₀| $ a₀ ∨S₀ b₀} {(|f₀| a₀) ∨FP₀ (|f₀| b₀)} (|f₀|-∨ a₀ b₀)) p₀∈|f₀|a₀∨|f₀|b₀ 
        --]]]

        open Equivalence (|f|-prop (a ∨S b) (inj₁ p₀))

    p← p p∈|f|a∨|f|b | inj₂ (inj₂ (p∈|f|a , p∈|f|b)) with EFA.to  ⟨$⟩ p∈|f|a | EFB.to ⟨$⟩ p∈|f|b 
      where
        module EFA = Equivalence (|f|-prop a p)
        module EFB = Equivalence (|f|-prop b p)
    p← (inj₁ p₀) p∈|f|a∨|f|b | inj₂ (inj₂ (p∈|f|a , p∈|f|b)) | (p₀' , ₁∼₁ p₀≈p₀' , p₀'∈|f₀|a₀) | (p₀'' , ₁∼₁ p₀≈p₀'' , p₀''∈|f₀|b₀) =
      from ⟨$⟩ (p₀ , ₁∼₁ ≈P₀-refl , p₀∈|f₀|a₀∨b₀)
      where
        open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)

        p₀∈|f₀|a₀ : p₀ ∈P₀ |f₀| a₀
        p₀∈|f₀|a₀ = ∈-resp-≈ ≈P₀-setoid (≈P₀-sym p₀≈p₀') p₀'∈|f₀|a₀

        p₀∈|f₀|b₀ : p₀ ∈P₀ |f₀| b₀
        p₀∈|f₀|b₀ = ∈-resp-≈ ≈P₀-setoid (≈P₀-sym p₀≈p₀'') p₀''∈|f₀|b₀

        p₀∈|f₀|a₀∨|f₀|b₀ : p₀ ∈P₀ ((|f₀| a₀) ∨FP₀ (|f₀| b₀))
        --[[[
        p₀∈|f₀|a₀∨|f₀|b₀ = 
          from ⟨$⟩ (inj₂ $ inj₂ (p₀∈|f₀|a₀ , p₀∈|f₀|b₀))
          where
            open Equivalence (FP₀.x∈∨⇔P∨ (|f₀| a₀) (|f₀| b₀) ((|f₀| a₀) ∨FP₀ (|f₀| b₀)) (LPW.refl ≈P₀-refl) p₀)
        --]]]

        p₀∈|f₀|a₀∨b₀ : p₀ ∈P₀ (|f₀| (a₀ ∨S₀ b₀))
        --[[[
        p₀∈|f₀|a₀∨b₀ = 
          FP₀.p∈c1≈c2 {p₀} {(|f₀| a₀) ∨FP₀ (|f₀| b₀)} {|f₀| (a₀ ∨S₀ b₀)} 
                       (≈FP₀-sym {|f₀| (a₀ ∨S₀ b₀)} {(|f₀| a₀) ∨FP₀ (|f₀| b₀)} (|f₀|-∨ a₀ b₀)) p₀∈|f₀|a₀∨|f₀|b₀ 
        --]]]        

        open Equivalence (|f|-prop (a ∨S b) (inj₁ p₀))
    --]]]

    sameElements : (p : |P|) → (p ∈P (|f| $ a ∨S b)) ⇔ (p ∈P ((|f| a) ∨FP (|f| b)))
    sameElements p = equivalence (p→ p) (p← p)
 
    open Equivalence (FP.c1≈c2⇔sameElements (|f| $ a ∨S b) ((|f| a) ∨FP (|f| b)))
f-∨ (inj₁ a₀) (inj₂ tt) =
  begin
    (|f| $ (inj₁ a₀ ∨S inj₂ tt)) 
      ≡⟨ PE.refl ⟩
    (|f| $ inj₂ tt) 
      ≈⟨ FP.≈-sym  {(|f| $ inj₁ a₀) FP.∨ (|f| $ inj₂ tt)} {|f| $ inj₂ tt} |f|inj₁a₀∨|f|inj₂tt≈|f|inj₂tt ⟩ 
    (|f| $ inj₁ a₀) FP.∨ (|f| $ inj₂ tt)
   ∎
  where
    open import Relation.Binary.EqReasoning (FP.FP-setoid)

    |f|inj₁a₀≤|f|inj₂tt : (|f| $ inj₁ a₀) FP.≤ (|f| $ inj₂ tt)
    |f|inj₁a₀≤|f|inj₂tt = LAll.tabulate tab
      where
        tab : {p : |P|} → p ∈≡ (proj₁ $ |f| (inj₁ a₀)) → Any (p ⊑P_) (proj₁ $ |f| (inj₂ tt))
        tab {p} p∈|f|inj₁a₀ with to ⟨$⟩ (LAny.map ≈P-reflexive p∈|f|inj₁a₀)
          where
            open Equivalence (|f|-prop (inj₁ a₀) p)
        tab {inj₁ p₀} p∈|f|inj₁a₀ | (p₀' , p≈inj₁p₀' , p₀'∈|f₀|a₀) =
          here (₁∼₂ tt)
        tab {inj₂ p₀} p∈|f|inj₁a₀ | (p₀' , () , p₀'∈|f₀|a₀)

    |f|inj₁a₀∨|f|inj₂tt≈|f|inj₂tt : ((|f| $ inj₁ a₀) FP.∨ (|f| $ inj₂ tt)) ≈FP (|f| $ inj₂ tt)
    |f|inj₁a₀∨|f|inj₂tt≈|f|inj₂tt = connecting→ {A = FP.FP-JS} (|f| $ inj₁ a₀) (|f| $ inj₂ tt) |f|inj₁a₀≤|f|inj₂tt
f-∨ (inj₂ tt) (inj₁ b₀) = 
  begin
    (|f| $ (inj₂ tt ∨S inj₁ b₀)) 
      ≡⟨ PE.refl ⟩
    (|f| $ inj₂ tt) 
      ≈⟨ FP.≈-sym  {(|f| $ inj₁ b₀) FP.∨ (|f| $ inj₂ tt)} {|f| $ inj₂ tt} |f|inj₁b₀∨|f|inj₂tt≈|f|inj₂tt ⟩ 
    (|f| $ inj₁ b₀) FP.∨ (|f| $ inj₂ tt)
      ≈⟨ FP.∨-comm (|f| $ inj₁ b₀) (|f| $ inj₂ tt) ⟩ 
    (|f| $ inj₂ tt) FP.∨ (|f| $ inj₁ b₀)
   ∎
  where
    open import Relation.Binary.EqReasoning (FP.FP-setoid)

    |f|inj₁b₀≤|f|inj₂tt : (|f| $ inj₁ b₀) FP.≤ (|f| $ inj₂ tt)
    |f|inj₁b₀≤|f|inj₂tt = LAll.tabulate tab
      where
        tab : {p : |P|} → p ∈≡ (proj₁ $ |f| (inj₁ b₀)) → Any (p ⊑P_) (proj₁ $ |f| (inj₂ tt))
        tab {p} p∈|f|inj₁b₀ with to ⟨$⟩ (LAny.map ≈P-reflexive p∈|f|inj₁b₀)
          where
            open Equivalence (|f|-prop (inj₁ b₀) p)
        tab {inj₁ p₀} p∈|f|inj₁b₀ | (p₀' , p≈inj₁p₀' , p₀'∈|f₀|b₀) =
          here (₁∼₂ tt)
        tab {inj₂ p₀} p∈|f|inj₁b₀ | (p₀' , () , p₀'∈|f₀|b₀)

    |f|inj₁b₀∨|f|inj₂tt≈|f|inj₂tt : ((|f| $ inj₁ b₀) FP.∨ (|f| $ inj₂ tt)) ≈FP (|f| $ inj₂ tt)
    |f|inj₁b₀∨|f|inj₂tt≈|f|inj₂tt = connecting→ {A = FP.FP-JS} (|f| $ inj₁ b₀) (|f| $ inj₂ tt) |f|inj₁b₀≤|f|inj₂tt
f-∨ (inj₂ tt) (inj₂ tt) = ∨-idempotent FP.FP-JS (|f| $ inj₂ tt)
  where
    open import Relation.Binary.Properties.JoinSemilattice
--]]]

decompose' : (c : List |P|) → IsFreeList c → 
             (Σ[ c' ∈ FP₀.SemilatCarrier ] LPW.Pointwise (λ x y → y ≡ inj₁ x) (proj₁ c') c) ⊎ (c ≡ (inj₂ tt ∷ []))
decompose' [] []-Free = inj₁ (([] , FP₀.[]-Free) , [])
decompose' (inj₁ x ∷ t) (∷-Free .(inj₁ x) .t min incomp ft) = 
  {!!}
  where
    rest : Σ[ t' ∈ FP₀.SemilatCarrier ] LPW.Pointwise (λ x y → y ≡ inj₁ x) (proj₁ t') t
    rest with decompose' t ft
    rest | inj₁ ((t' , ft') , t≡inj₁t') = {!!}
    rest | inj₂ t≡inj₂tt∷[] rewrite t≡inj₂tt∷[] = ⊥-elim $ incomp (here $ inj₁ (₁∼₂ tt))
decompose' (inj₂ tt ∷ []) fc = inj₂ PE.refl
decompose' (inj₂ tt ∷ inj₁ p₀ ∷ t) (∷-Free _ _ _ incomp _) = ⊥-elim $ incomp (here $ inj₂ (₁∼₂ tt))
decompose' (inj₂ tt ∷ inj₂ tt ∷ t) (∷-Free _ _ _ incomp _) = ⊥-elim $ incomp (here $ inj₁ (₂∼₂ $ record {}))
 
decompose : (c : FP.SemilatCarrier) → 
            (Σ[ c' ∈ FP₀.SemilatCarrier ] 
              LPW.Pointwise (λ x y → y ≡ inj₁ x) (proj₁ c') (proj₁ c)) ⊎ (proj₁ c ≡ (inj₂ tt ∷ []))
decompose (c , f) = decompose' c f

|g₀| = proj₁ $ SemSemilatIso.g semSemilatContent
|g₀|-≈ = proj₁ $ proj₂ $ SemSemilatIso.g semSemilatContent
|g₀|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilatIso.g semSemilatContent
|g₀|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilatIso.g semSemilatContent

|g| : FP.SemilatCarrier → |S|
|g| c with decompose c
|g| (c , f) | inj₁ ((c' , f') , c≡inj₁c') = inj₁ $ |g₀| (c' , f')
|g| (c , f) | inj₂ _ = inj₂ tt

|g|-≈ : (a b : FP.SemilatCarrier) → a ≈FP b → (|g| a) ≈S (|g| b)
--[[[
|g|-≈ a b a≈b with decompose a | decompose b
|g|-≈ a b a≈b | inj₁ ((a' , fa') , a≡inj₁a') | inj₁ ((b' , fb') , b≡inj₁b') = 
  ₁∼₁ $ |g₀|-≈ (a' , fa') (b' , fb') a'≈b'
  where
    inj₁a'≈a : LPW.Pointwise (λ a' a → inj₁ a' ≈P a) a' (proj₁ a)
    inj₁a'≈a = LPW.map ≈P-reflexive (LPW.map PE.sym a≡inj₁a')

    b≈inj₁b' : LPW.Pointwise (λ b b' → b ≈P inj₁ b') (proj₁ b) b'
    b≈inj₁b' = LPW.symmetric ≈P-sym $ LPW.map ≈P-reflexive (LPW.map PE.sym b≡inj₁b')

    inj₁a'≈b : LPW.Pointwise (λ a' b → inj₁ a' ≈P b) a' (proj₁ b)
    inj₁a'≈b = LPW.transitive ≈P-trans inj₁a'≈a a≈b

    inj₁a'≈inj₁b' : LPW.Pointwise (λ a' b' → inj₁ a' ≈P inj₁ b') a' b'
    inj₁a'≈inj₁b' = LPW.transitive ≈P-trans inj₁a'≈b b≈inj₁b'

    a'≈b' : (a' , fa') ≈FP₀ (b' , fb')
    a'≈b' = LPW.map aux inj₁a'≈inj₁b'
      where
        aux : {a' b' : |P₀|} → (inj₁ a' ≈P inj₁ b') → a' ≈P₀ b'
        aux {a'} {b'} (₁∼₁ a'≈b') = a'≈b'
|g|-≈ a b a≈b | inj₁ ((a' , fa') , a≡inj₁a') | inj₂ PE.refl 
  with (LPW.transitive ≈P-trans (LPW.map ≈P-reflexive (LPW.map PE.sym a≡inj₁a')) a≈b) 
|g|-≈ a b a≈b | inj₁ ((a' , fa') , a≡inj₁a') | inj₂ PE.refl | (₁∼₂ ()) ∷ _
|g|-≈ a b a≈b | inj₂ PE.refl | inj₁ ((b' , fb') , b≡inj₁b')
  with (LPW.transitive ≈P-trans a≈b (LPW.symmetric ≈P-sym (LPW.map ≈P-sym (LPW.map ≈P-reflexive b≡inj₁b'))))
|g|-≈ a b a≈b | inj₂ PE.refl | inj₁ ((b' , fb') , b≡inj₁b') | () ∷ _
|g|-≈ a b a≈b | inj₂ PE.refl | inj₂ PE.refl = ₂∼₂ PE.refl
--]]]

|g|-⊥ : |g| ⊥FP ≈S ⊥S
|g|-⊥ with decompose ⊥FP
|g|-⊥ | inj₁ (([] , []-Free) , []) = ₁∼₁ |g₀|-⊥ 
|g|-⊥ | inj₂ ()

{-
|g|-∨ : (a b : FP.SemilatCarrier) → (|g| $ a ∨FP b) ≈S ((|g| a) ∨S (|g| b))
|g|-∨ a b with decompose a | decompose b | decompose (a ∨FP b)

|g|-∨ a b | inj₁ ((a' , fa') , a≡inj₁a') | inj₁ ((b' , fb') , b≡inj₁b') | inj₁ ((a∨b' , f-a∨b') , a∨b≡inj₁a∨b') =
  {!!}
|g|-∨ a (.(inj₂ tt ∷ []) , snd) | inj₁ ((a' , fa') , a≡inj₁a') | inj₂ PE.refl | inj₁ (([] , fz) , a∨b≡inj₁a∨b') = {!!}
|g|-∨ a (.(inj₂ tt ∷ []) , snd) | inj₁ ((a' , fa') , a≡inj₁a') | inj₂ PE.refl | inj₁ ((x ∷ z , fz) , a∨b≡inj₁a∨b') = {!!}
|g|-∨ a b | inj₁ ((a' , fa') , a≡inj₁a') | inj₂ PE.refl | inj₂ _ = ₂∼₂ PE.refl
|g|-∨ a b | inj₂ PE.refl | inj₂ PE.refl | inj₂ PE.refl = ₂∼₂ PE.refl
-}

inv-FP→S→FP₀ : (a₀ : FP₀.SemilatCarrier) → (|f₀| $ |g₀| a₀) ≈FP₀ a₀
inv-FP→S→FP₀ = SemSemilatIso.inv-FP→S→FP semSemilatContent

inv-S→FP→S₀ : (a₀ : |S₀|) → (|g₀| $ |f₀| a₀) ≈S₀ a₀
inv-S→FP→S₀ = SemSemilatIso.inv-S→FP→S semSemilatContent

inv-FP→S→FP : (a : FP.SemilatCarrier) → (|f| $ |g| a) ≈FP a
--[[[
inv-FP→S→FP a with decompose a
inv-FP→S→FP a | inj₁ ((a' , fa') , a≡inj₁a') = from ⟨$⟩ sameElements
  where
    p→ : (p : |P|) → (p ∈P (|f| $ inj₁ $ |g₀| (a' , fa'))) → (p ∈P a)
    p→ p p∈|f|⋯ with to ⟨$⟩ p∈|f|⋯
      where
        open Equivalence (|f|-prop (inj₁ $ |g₀| (a' , fa')) p)
    p→ p p∈|f|⋯ | (p₀ , p≈inj₁p₀ , p₀∈|f₀||g₀|a') =
      LAny.map (≈P-trans p≈inj₁p₀) $ pointwiseRespAny imp a' (proj₁ a) p₀∈a' a≡inj₁a'
      where
        imp : {x₀ : |P₀|} → {x : |P|} → p₀ ≈P₀ x₀ → x ≡ inj₁ x₀ → inj₁ p₀ ≈P x
        imp {x₀} {x} p₀≈x₀ PE.refl = ₁∼₁ p₀≈x₀
        
        p₀∈a' : p₀ ∈P₀ (a' , fa')
        p₀∈a' = FP₀.p∈c1≈c2 {p₀} {|f₀| $ |g₀| (a' , fa')} {a' , fa'} (inv-FP→S→FP₀ (a' , fa')) p₀∈|f₀||g₀|a'
    
    p← : (p : |P|) → (p ∈P a) → (p ∈P (|f| $ inj₁ $ |g₀| (a' , fa')))
    p← p p∈a = anyEliminate a' elim p₀⋯
      where
        p₀⋯ : Any (λ · → p ≈P inj₁ ·) a'
        p₀⋯ = pointwiseRespAny imp (proj₁ a) a' p∈a (LPW.symmetric PE.sym a≡inj₁a')
          where
            imp : {x : |P|} → {y : |P₀|} → p ≈P x → inj₁ y ≡ x → (p ≈P inj₁ y)
            imp {x} {y} p≈x PE.refl = p≈x

        elim : AnyEliminator {ℓQ = l0} |P₀| (p ∈P (|f| $ inj₁ $ |g₀| (a' , fa'))) (λ · → p ≈P inj₁ ·) a'
        elim z f p≈inj₁z z∈a' = from ⟨$⟩ (z , p≈inj₁z , z∈|f₀||g₀|a')
          where
            open Equivalence (|f|-prop (inj₁ $ |g₀| (a' , fa')) p)
            
            z∈|f₀||g₀|a' : z ∈P₀ (|f₀| $ |g₀| (a' , fa'))
            z∈|f₀||g₀|a' = 
              FP₀.p∈c1≈c2 {z} {a' , fa'} {|f₀| $ |g₀| (a' , fa')} 
                          (FP₀.≈-sym {|f₀| $ |g₀| (a' , fa')} {a' , fa'} $ 
                          inv-FP→S→FP₀ (a' , fa')) (LAny.map ≈P₀-reflexive z∈a')
    
    sameElements : (p : |P|) → (p ∈P (|f| $ inj₁ $ |g₀| (a' , fa'))) ⇔ (p ∈P a)
    sameElements p = equivalence (p→ p) (p← p)

    open Equivalence (FP.c1≈c2⇔sameElements (|f| $ inj₁ $ |g₀| (a' , fa')) a)
inv-FP→S→FP .(inj₂ tt ∷ [] , _) | inj₂ PE.refl = ₂∼₂ PE.refl ∷ []
--]]]


inv-S→FP→S : (a : |S|) → (|g| $ |f| a) ≈S a
inv-S→FP→S a@(inj₁ a₀) with decompose (|f| $ inj₁ a₀)
inv-S→FP→S a@(inj₁ a₀) | inj₁ ((a' , fa') , |f|a≡inj₁a') = 
  begin
    (inj₁ $ |g₀| (a' , fa')) ≈⟨ ₁∼₁ eq ⟩ 
    a
   ∎
  where
    invaux-S→FP→S : (x : |P|) → (x ∈P (|f| $ inj₁ a₀)) ⇔ (P-|f| (inj₁ a₀) x)
    invaux-S→FP→S x = |f|-prop (inj₁ a₀) x

    |f₀|a₀≈a' : (|f₀| a₀) ≈FP₀ (a' , fa')
    |f₀|a₀≈a' = from ⟨$⟩ sameElements
      where
        p₀→ : (p₀ : |P₀|) → (p₀ ∈P₀ (|f₀| a₀)) → (p₀ ∈P₀ (a' , fa'))
        p₀→ p₀ p₀∈|f₀|a₀ = pointwiseRespAny⃖ imp a' (proj₁ $ |f| a) inj₁p₀∈|f|a |f|a≡inj₁a'
          where
            inj₁p₀∈|f|a : (inj₁ p₀) ∈P (|f| a)
            inj₁p₀∈|f|a = from ⟨$⟩ (p₀ , ₁∼₁ ≈P₀-refl , p₀∈|f₀|a₀)
              where
                open Equivalence (invaux-S→FP→S $ inj₁ p₀)

            imp : {x : |P₀|} → {y : |P|} → inj₁ p₀ ≈P y → y ≡ inj₁ x → p₀ ≈P₀ x
            imp {x} {y} (₁∼₁ p₀≈x) PE.refl = p₀≈x

        p₀← : (p₀ : |P₀|) → (p₀ ∈P₀ (a' , fa')) → (p₀ ∈P₀ (|f₀| a₀))
        p₀← p₀ p₀∈a' with to ⟨$⟩ inj₁p₀∈|f|a 
          where
            open Equivalence (invaux-S→FP→S $ inj₁ p₀)

            inj₁p₀∈|f|a : (inj₁ p₀) ∈P (|f| a)
            inj₁p₀∈|f|a = pointwiseRespAny imp a' (proj₁ $ |f| a) p₀∈a' |f|a≡inj₁a'
              where
                open Equivalence (invaux-S→FP→S $ inj₁ p₀)

                imp : {x : |P₀|} → {y : |P|} → p₀ ≈P₀ x → y ≡ inj₁ x → inj₁ p₀ ≈P y
                imp {x} {y} p₀≈x PE.refl = ₁∼₁ p₀≈x
        p₀← p₀ p₀∈a' | (p₀' , ₁∼₁ p₀≈p₀' , p₀'∈|f₀|a₀) = 
          ∈-resp-≈ ≈P₀-setoid (≈P₀-sym p₀≈p₀') p₀'∈|f₀|a₀
          where
            open import Data.List.Membership.Setoid.Properties
        
        sameElements : (p₀ : |P₀|) → (p₀ ∈P₀ (|f₀| a₀)) ⇔ (p₀ ∈P₀ (a' , fa'))
        sameElements p₀ = equivalence (p₀→ p₀) (p₀← p₀) 

        open Equivalence (FP₀.c1≈c2⇔sameElements (|f₀| a₀) (a' , fa'))
            
    eq : |g₀| (a' , fa') ≈S₀ a₀
    eq = 
      begin
        (|g₀| (a' , fa')) ≈⟨ |g₀|-≈ (a' , fa') (|f₀| a₀) (FP₀.≈-sym {|f₀| a₀} {a' , fa'} |f₀|a₀≈a') ⟩
        (|g₀| $ |f₀| a₀) ≈⟨ inv-S→FP→S₀ a₀ ⟩ 
        a₀
       ∎
      where
        open import Relation.Binary.EqReasoning ≈S₀-setoid

    open import Relation.Binary.EqReasoning ≈S-setoid
inv-S→FP→S (inj₁ a₀) | inj₂ eq with to ⟨$⟩ inj₂tt∈|f|inj₁a₀
  where
    open Equivalence (|f|-prop (inj₁ a₀) (inj₂ tt))

    inj₂tt∈|f|inj₁a₀ : (inj₂ tt) ∈P (|f| $ inj₁ a₀)
    inj₂tt∈|f|inj₁a₀ rewrite eq = here (₂∼₂ PE.refl)
inv-S→FP→S (inj₁ a₀) | inj₂ eq | (_ , () , _) 
inv-S→FP→S (inj₂ tt) = ₂∼₂ PE.refl 


