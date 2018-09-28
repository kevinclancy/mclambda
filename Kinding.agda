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


data IsPoset : τ → Set
data IsToset : τ → Set
data IsDeltaPoset : τ → Set 
data IsSemilat : τ → τ → Set

data IsPoset where
  FunPoset : {dom cod : τ} {q : q} → IsPoset dom → IsPoset cod → IsPoset (τFun dom q cod) 
  --DictPoset : {dom cod dCod : τ} → IsToset dom → IsSemilat cod dCod → IsPoset (τDict dom cod)
  --CapsulePoset : {q : q} {underlying : τ} → IsPoset underlying → IsPoset (τCapsule q underlying)
  ProductPoset : {τL τR : τ} → IsPoset τL → IsPoset τR → IsPoset (τProduct τL τR)
  SumPoset : {τL τR : τ} → IsPoset τL → IsPoset τR → IsPoset (τSum τL τR)
  --IVarPoset : {τContents : τ} → IsToset τContents → IsPoset (τIVar τContents)
  --PartialPoset : {τContents : τ} → IsPoset τContents → IsPoset (τPartial τContents)
  UnitPoset : IsPoset τUnit
  NatPoset : IsPoset τNat
  BoolPoset : IsPoset τBool

data IsToset where
  UnitToset : IsToset τUnit
  NatToset : IsToset τNat
  BoolToset : IsToset τBool
  ProductToset : {τL τR : τ} → IsToset τL → IsToset τR → IsToset (τProduct τL τR)
  SumToset : {τL τR : τ} → IsToset τL → IsToset τR → IsToset (τSum τL τR)
  -- CapsuleToset : {τ₀ : τ} {q : q} → IsToset τ₀ → IsToset (τCapsule q τ₀)
  -- PartialToset : {τ₀ : τ} → IsToset τ₀ → IsToset (τPartial τ₀)

data IsDeltaPoset where
  UnitDelta : IsDeltaPoset τUnit
  NatDelta : IsDeltaPoset τNat
  -- DiscreteProductDelta : {τL τR : τ} → IsToset τL → IsDeltaPoset τR → IsDeltaPoset (τProduct (τCapsule qAny τL) τR)
  SumDelta : {τL τR : τ} → IsDeltaPoset τL → IsDeltaPoset τR → IsDeltaPoset (τSum τL τR)
  -- DiscreteDelta : {τ₀ : τ} → IsToset τ₀ → IsDeltaPoset (τCapsule qAny τ₀) 
  -- PartialDelta : {τ₀ : τ} → IsDeltaPoset τ₀ → IsDeltaPoset (τPartial τ₀)

data IsSemilat where
  NatSemilat : IsSemilat τNat τNat
  BoolSemilat : IsSemilat τBool τUnit
  --DictSemilat : {dom cod dCod : τ} → IsToset dom → IsSemilat cod dCod → 
  --              IsSemilat (τDict dom cod) (τProduct (τCapsule qAny dom) dCod) 
  ProductSemilat : {τL τR τL₀ τR₀ : τ} → IsSemilat τL τL₀ → IsSemilat τR τR₀ → IsSemilat (τProduct τL τR) (τSum τL₀ τR₀)
  --IVarSemilat : {τ : τ} → IsToset τ → IsSemilat (τIVar τ) (τCapsule qAny τ)
  --PartialSemilat : {τ τ₀ : τ} → IsSemilat τ τ₀ → IsSemilat (τPartial τ) (τPartial τ₀)

semilat→delta : {τ τ₀ : τ} → (p : IsSemilat τ τ₀) → IsDeltaPoset τ₀
semilat→delta NatSemilat = NatDelta
semilat→delta BoolSemilat = UnitDelta
--semilat→delta (DictSemilat domIsToset codIsSemilat) = 
--  DiscreteProductDelta domIsToset (semilat→delta codIsSemilat) 
semilat→delta (ProductSemilat isSemilatL isSemilatR) = 
  SumDelta (semilat→delta isSemilatL) (semilat→delta isSemilatR)
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
