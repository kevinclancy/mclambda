open import SemilatKinding.Core
open import Relation.Binary
open import Deltas
open import Level 
open import Syntax
open import Kinding
open import Util

module SemilatKinding.Dictionary
  {τK τV τV₀ : τ}
  {isSemilatV : IsSemilat τV τV₀}
  (isStosetK : IsStoset τK)
  (semSemilatV : SemSemilatIso l0 l0 l0 l0 l0 l0 l0 isSemilatV)
 where

open import Data.Sum
open import Data.Product
open import Data.List
open import Data.List.All as LA
open import Data.List.Any as LAny
open import Data.List.Relation.Pointwise as LPW
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.Lattice
open import Function using (_$_ ; const)
open import Function.Equivalence
open import Function.Equality using (_⟨$⟩_)
open import FreeForgetfulAdjunction
open import SemKinding
open import Dictionary (SemStoset.T ⟦ isStosetK ⋇⟧) (SemSemilatCore.S ⟦ isSemilatV Δ⟧) renaming (_<_ to _<k_)

semilatCore = ⟦ DictSemilat isStosetK isSemilatV Δ⟧

P : DeltaPoset {l0} {l0} {l0} {l0}
P = SemSemilatCore.P semilatCore

bjsV = SemSemilatCore.S ⟦ isSemilatV Δ⟧
deltaV = SemSemilatCore.P ⟦ isSemilatV Δ⟧

|P| = DeltaPoset.Carrier P
|V₀| = DeltaPoset.Carrier deltaV

_∦P_ = DeltaPoset._∦_ P
_∥P_ = DeltaPoset._∥_ P
_≈P_ = DeltaPoset._≈_ P
_∦V₀_ = DeltaPoset._∦_ deltaV
_≈V₀_ = DeltaPoset._≈_ deltaV

≈V₀-reflexive = DeltaPoset.reflexive≈ deltaV
≈V₀-sym = DeltaPoset.sym≈ deltaV

≈P-reflexive = DeltaPoset.reflexive≈ P
≈P-sym = DeltaPoset.sym≈ P

_<P_ = DeltaPoset._<_ P
_<V₀_ = DeltaPoset._<_ deltaV

open import FreeSemilattice P renaming 
  (⊥ to ⊥F ; _∨_ to _∨F_ ; _≈_ to _≈F_ ; _~_ to _~F_ ; ≈-refl to ≈F-refl ; SemilatCarrier to Carrier-FP ;
   ≈-reflexive to ≈F-reflexive ; FP-BJS to FP-BJS ; ∨-identityˡ to ∨F-identityˡ ; ∨-identityʳ to ∨F-identityʳ ; 
   ⊑-refl to ⊑P-refl ; ⊑-reflexive to ⊑P-reflexive ; ⊑-trans to ⊑P-trans ; ⊑-decPoset to ⊑P-decPoset ;
   ≈-sym to ≈F-sym ; ∨-congˡ to ∨F-congˡ ; ∨-congʳ to ∨F-congʳ ; ∨-assoc to ∨F-assoc ; ∨-comm to ∨F-comm ;
   _∈_ to _∈P_ ; _∈'_ to _∈P'_ ; FP-setoid to FP-setoid ; c1≈c2⇔sameElements to c1≈c2⇔sameElementsP ;
   P∨ to P-P∨ ; x∈∨⇔P∨ to x∈∨⇔P∨-P ; p∈c1≈c2 to p∈c1≈c2-P ; concat-F to concat-F) 

open import FreeSemilattice deltaV renaming 
  (IsFreeList to IsFreeListV ; []-Free to []-FreeV ; ∷-Free to ∷-FreeV ; _≈_ to _≈FPV_ ; ⊥ to ⊥FPV ; 
   SemilatCarrier to Carrier-FPV ; _∨_ to _∨FPV_ ; FP-BJS to FPV-BJS ; FP-setoid to FPV-setoid ;
   ∨-identityˡ to ∨FV-identityˡ ; ∨-identityʳ to ∨FV-identityʳ ; ⊑-refl to ⊑V₀-refl ; ⊑-reflexive to ⊑V₀-reflexive ;
   ⊑-trans to ⊑V₀-trans ; ⊑-respˡ-≈ to ⊑V₀-respˡ-≈V₀ ; ⊑-respʳ-≈ to ⊑L₀-respʳ-≈L₀ ; 
   sng-free to sng-freeV ; _≤_ to _≤FV_ ; ≈-sym to ≈FV-sym ; ≈-trans to ≈FV-trans ; ≈-refl to ≈FV-refl ; 
   ≈-reflexive to ≈FV-reflexive ; 
   _∈_ to _∈V_ ; _∈'_ to _∈V'_ ;
   c1≈c2⇔sameElements to c1≈c2⇔sameElementsV ; p∈c1≈c2 to p∈c1≈c2-V ; x∈∨⇔P∨ to x∈∨⇔P∨-V ;
   concat-F to concat-FV)

|fV| : |V| → Σ[ l ∈ List (DeltaPoset.Carrier deltaV) ] (IsFreeListV l)
|fV| = proj₁ $ SemSemilatIso.f semSemilatV

|fV|-≈ : ∀ (a b : |V|) → a ≈v b → (|fV| a) ≈FPV (|fV| b)
|fV|-≈ = proj₁ $ proj₂ $ SemSemilatIso.f semSemilatV

|fV|-⊥ : |fV| ⊥v ≈FPV ⊥FPV
|fV|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilatIso.f semSemilatV

|fV|-∨ : ∀ (a b : |V|) → |fV| (a ∨v b) ≈FPV ( (|fV| a) ∨FPV (|fV| b) ) 
|fV|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilatIso.f semSemilatV

P-|f| : (d : ▹-Ty) → (x : |P|) → Set
P-|f| d (kx , vx) = Σ[ v ∈ |V| ] ((kx , v) ∈d d) × (vx ∈V |fV| v)

convV : (k : |K|) → (z : List |V₀|) → (f : IsFreeListV z) →  
      Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x y → y ≡ (k , x)) z (proj₁ l))
--[[[
convV k [] []-Free = ([] , []-Free) , []
convV k (v₀ ∷ t) (∷-Free v₀ t min incomp ft) = 
  ((k , v₀) ∷ t' , ∷-Free (k , v₀) t' min' incomp' ft') , (PE.refl ∷ eqt') 
  where
    rest : Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x y → y ≡ (k , x)) t (proj₁ l))
    rest = convV k t ft

    t' : List |P|
    t' = proj₁ $ proj₁ rest

    ft' : IsFreeList t'
    ft' = proj₂ $ proj₁ rest

    eqt' : LPW.Pointwise (λ x y → y ≡ (k , x)) t t'
    eqt' = proj₂ rest

    imp1 : {a : |V₀|} → {b : |P|} → (v₀ <V₀ a) → b ≡ (k , a) → (k , v₀) <P b
    imp1 {a} {b} v₀<a PE.refl = inj₂ (≈k-refl {k} , v₀<a)

    min' : All (λ z → (k , v₀) <P z) t'
    min' = pointwiseRespAll imp1 t t' min eqt'

    incomp' : ¬ LAny.Any (λ z → (k , v₀) ∦P z) t'
    --[[[
    incomp' kv₀∦z = anyEliminate t' eliminator kv₀∦z 
      where
        eliminator : AnyEliminator {ℓQ = l0} |P| ⊥ ((k , v₀) ∦P_) t'
        eliminator p@(pk , pv) f (inj₁ (k≈pk , v₀⊑pv)) p∈t' = incomp (pointwiseRespAny⃖ imp t t' p∈t' eqt')
          where
            imp : {a : |V₀|} → {b : |P|} → (pk , pv) ≡ b → b ≡ (k , a) → v₀ ∦V₀ a
            imp {a} {b} PE.refl PE.refl = inj₁ v₀⊑pv
        eliminator p@(pk , pv) f (inj₂ (pk≈k , pv⊑v₀)) p∈t' = incomp (pointwiseRespAny⃖ imp t t' p∈t' eqt')
          where
            imp : {a : |V₀|} → {b : |P|} → (pk , pv) ≡ b → b ≡ (k , a) → v₀ ∦V₀ a
            imp {a} {b} PE.refl PE.refl = inj₂ pv⊑v₀
    --]]]  
--]]]

|f|-aux : (l : List $ |K| × |V|) → (d : IsDict l) → Σ[ c ∈ Carrier-FP ] ∀ (x : |P|) → x ∈P c ⇔ P-|f| (l , d) x
|f|-aux [] []-Dict = ([] , []-Free) , equiv
  where
    x→ : (x : |P|) → x ∈P ([] , []-Free) → P-|f| ([] , []-Dict) x
    --[[[
    x→ x x∈[] = ⊥-elim $ ¬Any[] x∈[]
      where
        open import Data.List.Any.Properties
    --]]]

    x← : (x : |P|) → P-|f| ([] , []-Dict) x → x ∈P ([] , []-Free)
    --[[[
    x← x (v , inj₁ kv∈[] , _) = ⊥-elim $ ¬Any[] kv∈[]
      where
        open import Data.List.Any.Properties
    x← (kx , vx) (v , inj₂ v≈⊥ , vx∈|fV|v) = 
      ⊥-elim $ ¬Any[] (p∈c1≈c2-V {vx} {|fV| v} {[] , []-FreeV} |fV|v≈[] vx∈|fV|v)
      where
        open import Data.List.Any.Properties
        open import Data.List.Relation.Pointwise as LPW

        |fV|v≈[] : (|fV| v) ≈FPV ([] , []-FreeV)
        |fV|v≈[] = LPW.transitive (DeltaPoset.trans≈ deltaV) (|fV|-≈ v ⊥v v≈⊥) |fV|-⊥
    --]]]

    equiv : (x : |P|) → (x ∈P ([] , []-Free)) ⇔ P-|f| ([] , []-Dict) x
    --[[[
    equiv x = equivalence (x→ x) (x← x)
    --]]]
|f|-aux l@((k , v) ∷ t) dl@(∷-Dict (k , v) t min ¬v≈⊥ dt) = 
   (proj₁ res) , {!!}
  where
    open import Data.List.Any.Properties using (++⁻ ; ++⁺ʳ)

    |fV|v : Carrier-FPV
    |fV|v = |fV| v
    
    heads : Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x y → y ≡ (k , x)) (proj₁ |fV|v) (proj₁ l))
    heads = convV k (proj₁ |fV|v) (proj₂ |fV|v) 

    lheads : List |P|
    lheads = proj₁ $ proj₁ heads

    fheads : IsFreeList lheads
    fheads = proj₂ $ proj₁ heads

    eqheads : LPW.Pointwise (λ x y → y ≡ (k , x)) (proj₁ |fV|v) lheads
    eqheads = proj₂ heads

    rest : Σ[ c ∈ Carrier-FP ] ∀ (x : |P|) → x ∈P c ⇔ P-|f| (t , dt) x
    rest = |f|-aux t dt
    
    rest' : Carrier-FP
    rest' = proj₁ rest

    P-rest' : ∀ (x : |P|) → x ∈P rest' ⇔ P-|f| (t , dt) x
    P-rest' = proj₂ rest

    res : Σ[ c ∈ Carrier-FP ] (proj₁ c) ≡ (lheads ++ (proj₁ rest'))
    --[[[
    res = concat-F (proj₁ heads) rest' min' incomp' 
      where
        incomp' : All (λ x → All (x ∥P_) (proj₁ rest')) lheads
        --[[[
        incomp' = LA.tabulate tab
          where
            tab : {x : |K| × |V₀|} → x ∈≡ lheads → All (x ∥P_) (proj₁ rest')
            tab {x@(xk , xv₀)} x∈≡lheads = LA.tabulate tab'
              where
                xk≈k' : Any (const (xk ≈k k)) (proj₁ |fV|v)
                xk≈k' = pointwiseRespAny⃖ imp (proj₁ |fV|v) lheads x∈≡lheads eqheads  
                  where
                    imp : {a : |V₀|} → {b : |P|} → (xk , xv₀) ≡ b → b ≡ (k , a) → const (xk ≈k k) a
                    imp {a} {b} PE.refl PE.refl = ≈k-refl {k}

                xk≈k : xk ≈k k
                xk≈k = anyEliminate (proj₁ |fV|v) eliminator xk≈k'
                  where 
                    eliminator : AnyEliminator {ℓQ = l0} |V₀| (xk ≈k k) (const (xk ≈k k)) (proj₁ |fV|v)
                    eliminator _ _ xk≈k _ = xk≈k

                tab' : {y : |K| × |V₀|} → y ∈≡ (proj₁ rest') → (xk , xv₀) ∥P y
                tab' {y@(yk , yv₀)} y∈≡rest' x∦y with xk<yk  
                  where
                    module EY = Equivalence (P-rest' y)

                    P-|f|-y : P-|f| (t , dt) (yk , yv₀)
                    P-|f|-y = EY.to ⟨$⟩ (LAny.map (DeltaPoset.Eq.reflexive P) y∈≡rest') 

                    k<yk : k <k yk
                    k<yk with P-|f|-y
                    k<yk | v₀ , inj₁ ykv₀∈t , yv∈|fV|v₀ = anyEliminate t eliminator ykv₀∈t
                      where
                        eliminator : AnyEliminator {ℓQ = l0} (|K| × |V|) (k <k yk) ((yk , v₀) ≤e_) t
                        eliminator (ak , av) f (ak≈yk , av≤v₀) a∈t = <-respʳ-≈ (≈k-sym ak≈yk) k<ak
                          where
                            k<ak : k <k ak
                            k<ak = LA.lookup min a∈t
                    k<yk | v₀ , inj₂ v₀≈⊥ , yv∈|fV|v₀ = ⊥-elim (¬Any[] (p∈c1≈c2-V {yv₀} {|fV| v₀} {⊥FPV} fv₀≈⊥ yv∈|fV|v₀))
                      where
                        open import Data.List.Any.Properties
                        fv₀≈⊥ : (|fV| v₀) ≈FPV ⊥FPV
                        fv₀≈⊥ = begin
                          |fV| v₀ ≈⟨ |fV|-≈ v₀ ⊥v v₀≈⊥ ⟩
                          |fV| ⊥v ≈⟨ |fV|-⊥ ⟩
                          ⊥FPV
                         ∎
                          where
                            open import Relation.Binary.EqReasoning (preorder→setoid $ BoundedJoinSemilattice.preorder FPV-BJS)
                    
                    xk<yk : xk <k yk
                    xk<yk = <-respˡ-≈ (≈k-sym xk≈k) k<yk

                tab' {yk , yv₀} y∈≡rest' (inj₁ (xk≈yk , xv⊑yv)) | xk<yk = <-irrefl xk≈yk xk<yk 
                tab' {yk , yv₀} y∈≡rest' (inj₂ (yk≈xk , yv⊑xv)) | xk<yk = <-irrefl (≈k-sym yk≈xk) xk<yk 
        --]]]

        min' : All (λ h → All (h <P_) $ proj₁ rest') lheads
        --[[[
        min' = LA.tabulate tab
          where
            tab : {x : |K| × |V₀|} → (x ∈≡ lheads) → All (x <P_) (proj₁ rest')
            tab {x@(xk , xv)} x∈≡lheads = LA.tabulate tab'
              where
                tab' : {z : |K| × |V₀|} → z ∈≡ (proj₁ rest') → x <P z
                tab' {z@(zk , zv)} z∈≡rest' = inj₁ (<-respˡ-≈ (≈k-sym xk≈k) k<zk)
                  where
                    module EZ = Equivalence (P-rest' z)

                    xk≈k' : Any (const (xk ≈k k)) (proj₁ |fV|v)
                    xk≈k' = pointwiseRespAny⃖ imp (proj₁ |fV|v) lheads x∈≡lheads eqheads  
                      where
                        imp : {a : |V₀|} → {b : |P|} → (xk , xv) ≡ b → b ≡ (k , a) → const (xk ≈k k) a
                        imp {a} {b} PE.refl PE.refl = ≈k-refl {k}

                    xk≈k : xk ≈k k
                    xk≈k = anyEliminate (proj₁ |fV|v) eliminator xk≈k'
                      where 
                        eliminator : AnyEliminator {ℓQ = l0} |V₀| (xk ≈k k) (const (xk ≈k k)) (proj₁ |fV|v)
                        eliminator _ _ xk≈k _ = xk≈k

                    P-|f|-z : P-|f| (t , dt) (zk , zv)
                    P-|f|-z = EZ.to ⟨$⟩ (LAny.map (DeltaPoset.Eq.reflexive P) z∈≡rest') 

                    k<zk : k <k zk
                    k<zk with P-|f|-z
                    k<zk | v₀ , inj₁ zkv₀∈t , zv∈|fV|v₀ = anyEliminate t eliminator zkv₀∈t
                      where
                        eliminator : AnyEliminator {ℓQ = l0} (|K| × |V|) (k <k zk) ((zk , v₀) ≤e_) t
                        eliminator (ak , av) f (ak≈zk , av≤v₀) a∈t = <-respʳ-≈ (≈k-sym ak≈zk) k<ak
                          where
                            k<ak : k <k ak
                            k<ak = LA.lookup min a∈t
                    k<zk | v₀ , inj₂ v₀≈⊥ , zv∈|fV|v₀ = ⊥-elim (¬Any[] (p∈c1≈c2-V {zv} {|fV| v₀} {⊥FPV} fv₀≈⊥ zv∈|fV|v₀))
                      where
                        open import Data.List.Any.Properties
                        fv₀≈⊥ : (|fV| v₀) ≈FPV ⊥FPV
                        fv₀≈⊥ = begin
                          |fV| v₀ ≈⟨ |fV|-≈ v₀ ⊥v v₀≈⊥ ⟩
                          |fV| ⊥v ≈⟨ |fV|-⊥ ⟩
                          ⊥FPV
                         ∎
                          where
                            open import Relation.Binary.EqReasoning (preorder→setoid $ BoundedJoinSemilattice.preorder FPV-BJS)
        --]]]         
    --]]]

    P-res→ : (x : |P|) → (x ∈P proj₁ res) → P-|f| ((k , v) ∷ t , ∷-Dict (k , v) t min ¬v≈⊥ dt) x
    P-res→ x@(xk , xv₀) x∈res rewrite proj₂ res with (++⁻ lheads {proj₁ rest'} x∈res)
    P-res→ x@(xk , xv₀) x∈res | inj₁ x∈lheads = anyEliminate (proj₁ |fV|v) elim q
      where
        open import Data.List.Membership.Setoid.Properties
        q : Any (λ v₀ → (xk , xv₀) ≈P (k , v₀)) (proj₁ |fV|v)
        q = pointwiseRespAny⃖ imp (proj₁ |fV|v) lheads x∈lheads eqheads
          where
            imp : {a : |V₀|} → {b : |P|} → (xk ≈k proj₁ b) × (xv₀ ≈V₀ proj₂ b) → b ≡ (k , a) → (xk , xv₀) ≈P (k , a)
            imp {a} {b} x≈b PE.refl = x≈b

        elim : AnyEliminator {ℓQ = l0} |V₀| (Σ[ v₁ ∈ |V| ] ((xk , v₁) ∈d (l , dl)) × (xv₀ ∈V (|fV| v₁))) (λ v₀ → (xk , xv₀) ≈P (k , v₀)) (proj₁ $ |fV|v)
        elim a f (xk≈k , xv₀≈a) a∈|fV|v = v , xkv∈d , xv₀∈|fV|v
          where
            xv₀∈|fV|v : xv₀ ∈V (|fV| v)
            xv₀∈|fV|v = ∈-resp-≈ (DeltaPoset.≈-setoid deltaV) (≈V₀-sym xv₀≈a) (LAny.map ≈V₀-reflexive a∈|fV|v)
            
            xkv∈d : (xk , v) ∈d ((k , v) ∷ t , ∷-Dict (k , v) t min ¬v≈⊥ dt)
            xkv∈d = inj₁ $ here (xk≈k , ≤v-refl)  

    P-res→ x@(xk , xv₀) x∈res | inj₂ x∈rest' with to ⟨$⟩ x∈rest'
      where
        open Equivalence (P-rest' x)
    P-res→ x@(xk , xv₀) x∈res | inj₂ x∈rest' | v₁ , (inj₁ xkv₁∈t) , xv₀∈|fV|v₁ = 
      v₁ , inj₁ (there xkv₁∈t) , xv₀∈|fV|v₁
    P-res→ x@(xk , xv₀) x∈res | inj₂ x∈rest' | v₁ , (inj₂ v₁≈⊥) , xv₀∈|fV|v₁ =
      v₁ , inj₂ v₁≈⊥ , xv₀∈|fV|v₁

{-
P-|f| : (d : ▹-Ty) → (x : |P|) → Set
P-|f| d (kx , vx) = Σ[ v ∈ |V| ] ((kx , v) ∈d d) × (vx ∈V |fV| v)
-}
