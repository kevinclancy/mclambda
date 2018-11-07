open import Syntax
open import Kinding
open import SemKinding
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Data.Product

open import Function using (_$_)
open import Deltas
open import Util

open import SemilatKinding.Core

module SemilatKinding.IVar 
  {τContent : τ}
  {isStosetContent : IsStoset τContent}
 where

S : BoundedJoinSemilattice l0 l0 l0
S = SemSemilatCore.S ⟦ IVarSemilat isStosetContent Δ⟧

|S| : Set
|S| = BoundedJoinSemilattice.Carrier S

_∨S_ = BoundedJoinSemilattice._∨_ S
⊥S = BoundedJoinSemilattice.⊥ S
_≈S_ = BoundedJoinSemilattice._≈_ S
≈S-refl = BoundedJoinSemilattice.Eq.refl S

P : DeltaPoset {l0} {l0} {l0} {l0}
P = SemSemilatCore.P ⟦ IVarSemilat isStosetContent Δ⟧ 

|P| : Set
|P| = DeltaPoset.Carrier P

import FreeSemilattice P as FP

|FP| = FP.SemilatCarrier
_∨FP_ = FP._∨_
⊥FP = FP.⊥
_≈FP_ = FP._≈_
≈FP-refl = FP.≈-refl

|f| : |S| → |FP|
|f| x = x

|f|-≈ : (a b : |S|) → a ≈S b → (|f| a) ≈FP (|f| b)
|f|-≈ a b a≈b = a≈b 

|f|-⊥ : (|f| ⊥S) ≈FP ⊥FP
|f|-⊥ = ≈FP-refl {⊥FP}

|f|-∨ : (a b : |S|) → (|f| $ a ∨S b) ≈FP ((|f| a) ∨FP (|f| b))
|f|-∨ a b = ≈FP-refl {a ∨FP b}

|g| : |FP| → |S|
|g| x = x

|g|-≈ : (a b : |FP|) → a ≈FP b → (|g| a) ≈S (|g| b)
|g|-≈ a b a≈b = a≈b 

|g|-⊥ : (|g| ⊥FP) ≈S ⊥S
|g|-⊥ = ≈S-refl {⊥S}

|g|-∨ : (a b : |FP|) → (|g| $ a ∨FP b) ≈S ((|g| a) ∨S (|g| b))
|g|-∨ a b = ≈S-refl {(|g| a) ∨S |g| b}

inv-FP→S→FP : (a : |FP|) → (|f| $ |g| a) ≈FP a
inv-FP→S→FP a = ≈FP-refl {a}

inv-S→FP→S : (a : |S|) → (|f| $ |g| a) ≈S a
inv-S→FP→S a = ≈S-refl {a}


sem : SemSemilatIso l0 l0 l0 l0 l0 l0 l0 (IVarSemilat isStosetContent)
sem = record
  { f = |f| , |f|-≈ , |f|-⊥ , |f|-∨
  ; g = |g| , |g|-≈ , |g|-⊥ , |g|-∨
  ; inv-S→FP→S = inv-FP→S→FP 
  ; inv-FP→S→FP = inv-S→FP→S 
  }



