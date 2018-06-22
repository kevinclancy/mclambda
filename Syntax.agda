module Syntax where

open import Scalars

open import Data.Nat

--types
data τ : Set where
  τFun : (dom : τ) → (scalar : q) → (cod : τ) → τ
  τDict : (dom : τ) → (cod : τ) → τ   
  τCapsule : (scalar : q) → (underlying : τ) → τ 
  τProduct : (τL : τ) → (τR : τ) → τ
  τSum : (τL : τ) → (τR : τ) → τ
  τIVar : τ → τ
  τPartial : τ → τ
  τUnit : τ
  τBool : τ 
  τNat : τ

--expressions
data e : Set where
  Bot : τ → e
  Join : τ → e → e → e
  Extract : (dict : e) → (body : e) → e
  Cons : (key : e) → (val : e) → (dict : e) → e
  Proj1 : (pair : e) → e
  Proj2 : (pair : e) → e
  Pair : (eL : e) → (eR : e) → e
  MLet : (first : e) → (andThen : e) → e
  Case : (scrut : e) → (lCase : e) → (rCase : e) → e
  Inl : (τL : τ) → (τR : τ) → e → e
  Inr : (τL : τ) → (τR : τ) → e → e
  -- coeffect capsule "cap q e"
  Cap : q → e → e
  -- let cap q x = e in e 
  Uncap : q → (capsule : e) → (body : e) → e
  Var : ℕ → e
  Abs : (body : e) → e
  App : (fun : e) → (arg : e) → e
  -- [ e ], promotes pure expression e to monotonically partial computation
  Pure : e → e
  Nat : ℕ → e
  -- unit value
  ∗ : e
  tt : e
  ff : e
  -- create a singleton ivar cell with specified contents 
  ICell : (contents : e) → e 
  --open an ivar cell: "let ⌈ x ⌉ = e in e"
  IOpen : (ivar : e) → (body : e) → e
  -- homomorphism definition: "hom (x : τDom). e"
  Hom : (τDom : τ) → (body : e) → e
 

-- data τ : Set where
--   Unit : τ
--   List : τ → τ
--   Product : τ → τ → τ
--   Sum : τ → τ → τ 
--   Fun : {numArgs : ℕ} → Vec τ numArgs → τ → τ

-- -- terms
-- data t : Set where
--   Var : ℕ → t
--   Pair : t → t → t
--   Proj1 : t → t
--   Proj2 : t → t
--   -- App fun arg
--   App : t → t → t
--   -- Abs body
--   Abs : t → t
--   -- Cons hd tl
--   Cons : t → t → t
--   -- ListCase tScrut tCaseNil tCaseCons
--   ListCase : t → t → t → t
--   -- SumCase tScrut tCaseL tCaseR
--   SumCase : t → t → t → t
--   UnitVal : t
--   -- LetRec dom cod body
--   LetRec : {n : ℕ} → Vec τ n → τ → t → t
