module Kinding where

open import PosetScalars
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
data IsSemilat : τ → τ → Set

data IsPoset where
  FunPoset : {dom cod : τ} {q : q} → IsPoset dom → IsPoset cod → IsPoset (τFun dom q cod) 
  DictPoset : {dom cod dCod : τ} → IsStoset dom → IsSemilat cod dCod → IsPoset (τDict dom cod)
  CapsulePoset : {underlying : τ} → (q' : q') → IsPoset underlying → IsPoset (τCapsule q' underlying)
  ProductPoset : {τL τR : τ} → IsPoset τL → IsPoset τR → IsPoset (τProduct τL τR)
  SumPoset : {τL τR : τ} → IsPoset τL → IsPoset τR → IsPoset (τSum τL τR)
  IVarPoset : {τContents : τ} → IsStoset τContents → IsPoset (τIVar τContents)
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
  PartialStoset : {τ₀ : τ} → IsStoset τ₀ → IsStoset (τPartial τ₀)

data IsSemilat where
  NatSemilat : IsSemilat τNat τNat
  BoolSemilat : IsSemilat τBool τUnit
  DictSemilat : {dom cod dCod : τ} → IsStoset dom → IsSemilat cod dCod → 
                IsSemilat (τDict dom cod) (τProduct (τCapsule qAny' dom) dCod) 
  ProductSemilat : {τL τR τL₀ τR₀ : τ} → IsSemilat τL τL₀ → IsSemilat τR τR₀ → IsSemilat (τProduct τL τR) (τSum τL₀ τR₀)
  IVarSemilat : {τ : τ} → IsStoset τ → IsSemilat (τIVar τ) (τCapsule qAny' τ)
  PartialSemilat : {τ τ₀ : τ} → IsSemilat τ τ₀ → IsSemilat (τPartial τ) (τPartial τ₀)

isSemilatDeltaUnique : {τ₀ τ₀' τ₀'' : τ} → (p : IsSemilat τ₀ τ₀') → (q : IsSemilat τ₀ τ₀'') → τ₀' ≡ τ₀''
isSemilatUnique : {τ₀ τ₀' : τ} → (p : IsSemilat τ₀ τ₀') → (q : IsSemilat τ₀ τ₀') → p ≡ q
isStosetUnique : {τ₀ : τ} → (p : IsStoset τ₀) → (q : IsStoset τ₀) → p ≡ q
isPosetUnique : {τ₀ : τ} → (p : IsPoset τ₀) → (q : IsPoset τ₀) → p ≡ q

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
isSemilatDeltaUnique {τIVar x} {τCapsule qAny' y} {τCapsule qAny' z} (IVarSemilat a) (IVarSemilat a') =
  PE.refl
isSemilatDeltaUnique {τDict x y} {τProduct (τCapsule qAny' x) z1} {τProduct (τCapsule qAny' x) z2} 
                     (DictSemilat _ codSemilat) (DictSemilat _ codSemilat') =
  PE.cong (τProduct (τCapsule qAny' x)) (isSemilatDeltaUnique codSemilat codSemilat')

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
isSemilatUnique {.(τIVar _)} {.(τCapsule qAny' _)} (IVarSemilat a) (IVarSemilat a')  =
  PE.cong IVarSemilat (isStosetUnique a a')
isSemilatUnique (DictSemilat domStoset codSemilat) (DictSemilat domStoset' codSemilat') =
  PE.cong₂ DictSemilat (isStosetUnique domStoset domStoset') (isSemilatUnique codSemilat codSemilat')

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
isPosetUnique {.(τIVar _)} (IVarPoset contentStoset) (IVarPoset contentStoset') =
  PE.cong IVarPoset (isStosetUnique contentStoset contentStoset')
isPosetUnique {τCapsule q' _} (CapsulePoset .q' contentPoset) (CapsulePoset .q' contentPoset') =
  PE.cong (CapsulePoset q') (isPosetUnique contentPoset contentPoset')

semilat→poset : {τ τ₀ : τ} → (p : IsSemilat τ τ₀) → IsPoset τ
stoset→poset : {τ₀ : τ} → IsStoset τ₀ → IsPoset τ₀
semilat→deltaPoset : {τ τ₀ : τ} → IsSemilat τ τ₀ → IsPoset τ₀

semilat→poset NatSemilat = NatPoset
semilat→poset BoolSemilat = BoolPoset
semilat→poset (ProductSemilat isSemilatL isSemilatR) = ProductPoset (semilat→poset isSemilatL) (semilat→poset isSemilatR)  
semilat→poset (PartialSemilat isSemilatContents) = PartialPoset (semilat→poset isSemilatContents)
semilat→poset (IVarSemilat isStosetContents) = IVarPoset isStosetContents
semilat→poset (DictSemilat isStosetDom isSemilatCod) = DictPoset isStosetDom isSemilatCod

semilat→deltaPoset BoolSemilat = UnitPoset
semilat→deltaPoset NatSemilat = NatPoset
semilat→deltaPoset (ProductSemilat isSemilatL isSemilatR) = 
  SumPoset (semilat→deltaPoset isSemilatL) (semilat→deltaPoset isSemilatR)
semilat→deltaPoset (PartialSemilat isSemilatContents) =
  PartialPoset (semilat→deltaPoset isSemilatContents)
semilat→deltaPoset (IVarSemilat isStosetContents) =
  CapsulePoset qAny' (stoset→poset isStosetContents)
semilat→deltaPoset (DictSemilat isStosetDom isSemilatCod) =
  ProductPoset (CapsulePoset qAny' (stoset→poset isStosetDom)) (semilat→deltaPoset isSemilatCod)

stoset→poset UnitStoset = UnitPoset
stoset→poset NatStoset = NatPoset
stoset→poset BoolStoset = BoolPoset
stoset→poset (ProductStoset isStosetL isStosetR) = ProductPoset (stoset→poset isStosetL) (stoset→poset isStosetR)
stoset→poset (SumStoset isStosetL isStosetR) = SumPoset (stoset→poset isStosetL) (stoset→poset isStosetR)
stoset→poset (PartialStoset isStosetContents) = PartialPoset (stoset→poset isStosetContents)
