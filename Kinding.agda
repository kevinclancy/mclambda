module Kinding where

open import Scalars
open import Syntax
open import FinPoset

open import Relation.Nullary
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality as PE

data IsPoset : τ → Set
data IsStoset : τ → Set
data IsDeltaPoset : τ → Set 
data IsSemilat : τ → τ → Set

data IsPoset where
  FunPoset : {dom cod : τ} {q : q} → IsPoset dom → IsPoset cod → IsPoset (τFun dom q cod) 
  DictPoset : {dom cod dCod : τ} → IsStoset dom → IsSemilat cod dCod → IsPoset (τDict dom cod)
  --CapsulePoset : {q : q} {underlying : τ} → IsPoset underlying → IsPoset (τCapsule q underlying)
  ProductPoset : {τL τR : τ} → IsPoset τL → IsPoset τR → IsPoset (τProduct τL τR)
  SumPoset : {τL τR : τ} → IsPoset τL → IsPoset τR → IsPoset (τSum τL τR)
  --IVarPoset : {τContents : τ} → IsToset τContents → IsPoset (τIVar τContents)
  PartialPoset : {τContents : τ} → IsPoset τContents → IsPoset (τPartial τContents)
  UnitPoset : IsPoset τUnit
  NatPoset : IsPoset τNat
  BoolPoset : IsPoset τBool

data IsStoset where
  UnitStoset : IsStoset τUnit
  NatStoset : IsStoset τNat
  BoolStoset : IsStoset τBool
  ProductStoset : {τL τR : τ} → IsStoset τL → IsStoset τR → IsStoset (τProduct τL τR)
  SumStoset : {τL τR : τ} → IsStoset τL → IsStoset τR → IsStoset (τSum τL τR)
  -- CapsuleToset : {τ₀ : τ} {q : q} → IsToset τ₀ → IsToset (τCapsule q τ₀)
  PartialStoset : {τ₀ : τ} → IsStoset τ₀ → IsStoset (τPartial τ₀)

data IsDeltaPoset where
  UnitDelta : IsDeltaPoset τUnit
  NatDelta : IsDeltaPoset τNat
  -- DiscreteProductDelta : {τL τR : τ} → IsToset τL → IsDeltaPoset τR → IsDeltaPoset (τProduct (τCapsule qAny τL) τR)
  SumDelta : {τL τR : τ} → IsDeltaPoset τL → IsDeltaPoset τR → IsDeltaPoset (τSum τL τR)
  -- DiscreteDelta : {τ₀ : τ} → IsToset τ₀ → IsDeltaPoset (τCapsule qAny τ₀) 
  PartialDelta : {τ₀ : τ} → IsDeltaPoset τ₀ → IsDeltaPoset (τPartial τ₀)

data IsSemilat where
  NatSemilat : IsSemilat τNat τNat
  BoolSemilat : IsSemilat τBool τUnit
  --DictSemilat : {dom cod dCod : τ} → IsToset dom → IsSemilat cod dCod → 
  --              IsSemilat (τDict dom cod) (τProduct (τCapsule qAny dom) dCod) 
  ProductSemilat : {τL τR τL₀ τR₀ : τ} → IsSemilat τL τL₀ → IsSemilat τR τR₀ → IsSemilat (τProduct τL τR) (τSum τL₀ τR₀)
  --IVarSemilat : {τ : τ} → IsToset τ → IsSemilat (τIVar τ) (τCapsule qAny τ)
  PartialSemilat : {τ τ₀ : τ} → IsSemilat τ τ₀ → IsSemilat (τPartial τ) (τPartial τ₀)

mutual
 isSemilatDeltaUnique : {τ₀ τ₀' τ₀'' : τ} → (p : IsSemilat τ₀ τ₀') → (q : IsSemilat τ₀ τ₀'') → τ₀' ≡ τ₀''
 isSemilatDeltaUnique {.τNat} {.τNat} {.τNat} NatSemilat NatSemilat = PE.refl
 isSemilatDeltaUnique {.τBool} {.τUnit} {.τUnit} BoolSemilat BoolSemilat = PE.refl
 isSemilatDeltaUnique {.(τProduct _ _)} {τSum τL τR} {τSum τL' τR'} (ProductSemilat l r) (ProductSemilat l' r') = 
   PE.cong₂ τSum eqL eqR
   where
     eqL : τL ≡ τL'
     eqL = isSemilatDeltaUnique l l'

     eqR : τR ≡ τR'
     eqR = isSemilatDeltaUnique r r'
 isSemilatDeltaUnique {τPartial x} {τPartial y} {τPartial z} (PartialSemilat a) (PartialSemilat a') = 
   PE.cong τPartial (isSemilatDeltaUnique a a')

 isSemilatUnique : {τ₀ τ₀' : τ} → (p : IsSemilat τ₀ τ₀') → (q : IsSemilat τ₀ τ₀') → p ≡ q
 isSemilatUnique {.τNat} {.τNat} NatSemilat NatSemilat = PE.refl
 isSemilatUnique {.τBool} {.τUnit} BoolSemilat BoolSemilat = PE.refl
 isSemilatUnique {.(τProduct _ _)} {.(τSum _ _)} (ProductSemilat l r) (ProductSemilat l' r') = 
   PE.cong₂ ProductSemilat eqL eqR
   where
     eqL : l ≡ l'
     eqL = isSemilatUnique l l'
     
     eqR : r ≡ r'
     eqR = isSemilatUnique r r'
 isSemilatUnique {.(τPartial _)} {.(τPartial _)} (PartialSemilat a) (PartialSemilat a')  =
   PE.cong PartialSemilat (isSemilatUnique a a')

 isStosetUnique : {τ₀ : τ} → (p : IsStoset τ₀) → (q : IsStoset τ₀) → p ≡ q
 isStosetUnique {.τUnit} UnitStoset UnitStoset = PE.refl
 isStosetUnique {.τNat} NatStoset NatStoset = PE.refl
 isStosetUnique {.τBool} BoolStoset BoolStoset = PE.refl
 isStosetUnique {.(τProduct _ _)} (ProductStoset pStosetL pStosetR) (ProductStoset qStosetL qStosetR) = 
   PE.cong₂ ProductStoset eqL eqR
   where
     eqL : pStosetL ≡ qStosetL
     eqL = isStosetUnique pStosetL qStosetL

     eqR : pStosetR ≡ qStosetR
     eqR = isStosetUnique pStosetR qStosetR
 isStosetUnique {.(τSum _ _)} (SumStoset pStosetL pStosetR) (SumStoset qStosetL qStosetR) = 
   PE.cong₂ (λ x y → SumStoset x y) eqL eqR
   where
     eqL : pStosetL ≡ qStosetL
     eqL = isStosetUnique pStosetL qStosetL

     eqR : pStosetR ≡ qStosetR
     eqR = isStosetUnique pStosetR qStosetR
 isStosetUnique {.(τPartial _)} (PartialStoset pStosetContents) (PartialStoset qStosetContents) = 
   PE.cong PartialStoset (isStosetUnique pStosetContents qStosetContents)

 isPosetUnique : {τ₀ : τ} → (p : IsPoset τ₀) → (q : IsPoset τ₀) → p ≡ q
 isPosetUnique {.(τFun _ _ _)} (FunPoset isPosetCod isPosetDom) (FunPoset isPosetCod' isPosetDom') = 
   PE.cong₂ FunPoset eqL eqR
   where
     eqL : isPosetCod ≡ isPosetCod'
     eqL = isPosetUnique isPosetCod isPosetCod'

     eqR : isPosetDom ≡ isPosetDom'
     eqR = isPosetUnique isPosetDom isPosetDom'
 isPosetUnique {.(τDict _ _)} (DictPoset isDomStoset isCodSemilat) (DictPoset isDomStoset' isCodSemilat') 
   with isSemilatDeltaUnique isCodSemilat isCodSemilat'
 isPosetUnique {.(τDict _ _)} (DictPoset isDomStoset isCodSemilat) (DictPoset isDomStoset' isCodSemilat') 
   | PE.refl =
   PE.cong₂ DictPoset domEq codEq
   where
     domEq : isDomStoset ≡ isDomStoset'
     domEq = isStosetUnique isDomStoset isDomStoset'

     codEq : isCodSemilat ≡ isCodSemilat'
     codEq = isSemilatUnique isCodSemilat isCodSemilat'

 isPosetUnique {.(τProduct _ _)} (ProductPoset isPosetL isPosetR) (ProductPoset isPosetL' isPosetR') =
   PE.cong₂ (λ x y → ProductPoset x y) eqL eqR
   where
     eqL : isPosetL ≡ isPosetL'
     eqL = isPosetUnique isPosetL isPosetL'

     eqR : isPosetR ≡ isPosetR'
     eqR = isPosetUnique isPosetR isPosetR'
 isPosetUnique {.(τSum _ _)} (SumPoset isPosetL isPosetR) (SumPoset isPosetL' isPosetR') = 
   PE.cong₂ (λ x y → SumPoset x y) eqL eqR
   where
     eqL : isPosetL ≡ isPosetL'
     eqL = isPosetUnique isPosetL isPosetL'

     eqR : isPosetR ≡ isPosetR'
     eqR = isPosetUnique isPosetR isPosetR'
 isPosetUnique {.(τPartial _)} (PartialPoset isPosetContents) (PartialPoset isPosetContents') =
   PE.cong PartialPoset (isPosetUnique isPosetContents isPosetContents')
 isPosetUnique {.τUnit} UnitPoset UnitPoset = PE.refl
 isPosetUnique {.τNat} NatPoset NatPoset = PE.refl
 isPosetUnique {.τBool} BoolPoset BoolPoset = PE.refl

semilat→poset : {τ τ₀ : τ} → (p : IsSemilat τ τ₀) → IsPoset τ
semilat→poset NatSemilat = NatPoset
semilat→poset BoolSemilat = BoolPoset
semilat→poset (ProductSemilat isSemilatL isSemilatR) = ProductPoset (semilat→poset isSemilatL) (semilat→poset isSemilatR)  
semilat→poset (PartialSemilat isSemilatContents) = PartialPoset (semilat→poset isSemilatContents)

semilat→delta : {τ τ₀ : τ} → (p : IsSemilat τ τ₀) → IsDeltaPoset τ₀
semilat→delta NatSemilat = NatDelta
semilat→delta BoolSemilat = UnitDelta
--semilat→delta (DictSemilat domIsToset codIsSemilat) = 
--  DiscreteProductDelta domIsToset (semilat→delta codIsSemilat) 
semilat→delta (ProductSemilat isSemilatL isSemilatR) = 
  SumDelta (semilat→delta isSemilatL) (semilat→delta isSemilatR)
semilat→delta (PartialSemilat isSemilatContents) = 
  PartialDelta (semilat→delta isSemilatContents)


stoset→poset : {τ₀ : τ} → IsStoset τ₀ → IsPoset τ₀
stoset→poset UnitStoset = UnitPoset
stoset→poset NatStoset = NatPoset
stoset→poset BoolStoset = BoolPoset
stoset→poset (ProductStoset isStosetL isStosetR) = ProductPoset (stoset→poset isStosetL) (stoset→poset isStosetR)
stoset→poset (SumStoset isStosetL isStosetR) = SumPoset (stoset→poset isStosetL) (stoset→poset isStosetR)
stoset→poset (PartialStoset isStosetContents) = PartialPoset (stoset→poset isStosetContents)

delta→poset : {τ₀ : τ} → IsDeltaPoset τ₀ → IsPoset τ₀
delta→poset UnitDelta = UnitPoset
delta→poset NatDelta = NatPoset
delta→poset (SumDelta deltaL deltaR) = SumPoset (delta→poset deltaL) (delta→poset deltaR) 
delta→poset (PartialDelta deltaContents) = PartialPoset (delta→poset deltaContents)

--semilat→delta (IVarSemilat contentIsToset) = 
--  DiscreteDelta contentIsToset
--semilat→delta (PartialSemilat contentIsSemilat) = 
--  PartialDelta (semilat→delta contentIsSemilat)


-- kCheckPoset : 
--   (σ : τ) → Dec( Σ[ S ∈ Set ] Σ[ refσ ∈ (S → Set) ] Σ[ ⊑ ∈ (S → S → Set) ] Σ[ ref⊑ ∈ (⊑ → Set) ] IsPoset σ )
-- kCheckPoset = {!!}

-- -- kCheckSemilat : (σ : τ) → Dec( Σ[ σ₀ ∈ τ ] IsSemilat σ σ₀ )
-- -- kCheckSemilat (τFun σ scalar σ₁) = no contr
-- --   where
-- --     contr : Σ[ σ₀ ∈ τ ] IsSemilat (τFun σ scalar σ₁) σ₀ → ⊥
-- --     contr (σ₀ , ())
-- -- kCheckSemilat (τDict σ σ₁) = {!!}
-- -- kCheckSemilat (τCapsule scalar σ) = no contr
-- --   where
-- --     contr  : Σ[ σ₀ ∈ τ ] IsSemilat (τCapsule scalar σ) σ₀ → ⊥
-- --     contr (σ₀ , ())
-- -- kCheckSemilat (τProduct σ σ₁) = {!!}
-- -- kCheckSemilat (τSum σ σ₁) = no contr
-- --   where
-- --     contr : Σ[ σ₀ ∈ τ ] IsSemilat (τSum σ σ₁) σ₀ → ⊥
-- --     contr (σ₀ , ())
-- -- kCheckSemilat (τIVar σ) = {!!}
-- -- kCheckSemilat (τPartial σ) = {!!}
-- -- kCheckSemilat τUnit = {!!}
-- -- kCheckSemilat τBool = {!!}
-- -- kCheckSemilat τNat = {!!}
