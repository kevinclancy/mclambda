module Scalars where

open import Function using (_∘_ ; _$_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE
open import Relation.Nullary
open import FinPoset
open import Data.Nat as N
open import Data.List as L
open import Data.List.Any
open import Data.Vec as V
open import Data.Fin as F
open import Data.Star
open import Data.Product

--scalars
data q : Set where
  qMono : q
  qAnti : q
  qConst : q
  qAny : q

_q=?_ : Decidable (_≡_ {A = q})
qMono q=? qMono = yes refl
qMono q=? qAnti = no (λ ())
qMono q=? qConst = no (λ ())
qMono q=? qAny = no (λ ())
qAnti q=? qMono = no (λ ())
qAnti q=? qAnti = yes refl
qAnti q=? qConst = no (λ ())
qAnti q=? qAny = no (λ ())
qConst q=? qMono = no (λ ())
qConst q=? qAnti = no (λ ())
qConst q=? qConst = yes refl
qConst q=? qAny = no (λ ())
qAny q=? qMono = no (λ ())
qAny q=? qAnti = no (λ ())
qAny q=? qConst = no (λ ())
qAny q=? qAny = yes refl

private
  depth : q → ℕ
  depth qAny = 0
  depth qMono = 1
  depth qAnti = 1
  depth qConst = 2

covers : List $ Cover q depth
covers = (qMono / qAny / ≤′-refl) ∷
         (qAnti / qAny / ≤′-refl) ∷
         (qConst / qMono / ≤′-refl) ∷
         (qConst / qAnti / ≤′-refl) ∷
         []

module QP = FinPoset.FinPoset q depth covers _q=?_ 

-- The finite "specificity" partial order on qualifiers 
_q≤_ : (q₀ q₁ : q) → Set
_q≤_ = QP._≤_

-- The finite "specificity" covering relation underlying _q≤_
_q≺_ : (q₀ q₁ : q) → Set
_q≺_ = QP._≺_

-- A decision procedure for _q≤_
_q≤?_ : (q₀ q₁ : q) → Dec (q₀ q≤ q₁)
_q≤?_ = QP._≤?_

q≤-isPreorder : IsPreorder _≡_ _q≤_
q≤-isPreorder = QP.≤-isPreorder

--qualifier composition
_q∘_ : q → q → q
qMono q∘ qMono = qMono
qMono q∘ qAnti = qAnti
qMono q∘ qConst = qConst
qMono q∘ qAny = qAny
qAnti q∘ qMono = qAnti
qAnti q∘ qAnti = qMono
qAnti q∘ qConst = qConst
qAnti q∘ qAny = qAny
qConst q∘ qMono = qConst
qConst q∘ qAnti = qConst
qConst q∘ qConst = qConst
qConst q∘ qAny = qConst
qAny q∘ qMono = qAny
qAny q∘ qAnti = qAny
qAny q∘ qConst = qConst
qAny q∘ qAny = qAny

--qualifier contraction
_q+_ : q → q → q
qMono q+ qMono = qMono
qMono q+ qAnti = qAny
qMono q+ qConst = qMono
qMono q+ qAny = qAny
qAnti q+ qMono = qAny
qAnti q+ qAnti = qAnti
qAnti q+ qConst = qAnti
qAnti q+ qAny = qAny
qConst q+ qMono = qMono
qConst q+ qAnti = qAnti
qConst q+ qConst = qConst
qConst q+ qAny = qAny
qAny q+ qMono = qAny
qAny q+ qAnti = qAny
qAny q+ qConst = qAny
qAny q+ qAny = qAny

q₁+q₂≤q₁ : ∀ {q₁ q₂ : q} → q₁ q≤ (q₁ q+ q₂)
q₁+q₂≤q₁ {qMono} {qMono} = ε
q₁+q₂≤q₁ {qMono} {qAnti} = here (PE.refl , PE.refl) ◅ ε
q₁+q₂≤q₁ {qMono} {qConst} = ε
q₁+q₂≤q₁ {qMono} {qAny} = here (PE.refl , PE.refl) ◅ ε
q₁+q₂≤q₁ {qAnti} {qMono} = there (here (PE.refl , PE.refl)) ◅ ε
q₁+q₂≤q₁ {qAnti} {qAnti} = ε
q₁+q₂≤q₁ {qAnti} {qConst} = ε
q₁+q₂≤q₁ {qAnti} {qAny} = there (here (PE.refl , PE.refl)) ◅ ε
q₁+q₂≤q₁ {qConst} {qMono} = (there (there (here (PE.refl , PE.refl)))) ◅ ε
q₁+q₂≤q₁ {qConst} {qAnti} = (there (there (there (here (PE.refl , PE.refl))))) ◅ ε
q₁+q₂≤q₁ {qConst} {qConst} = ε
q₁+q₂≤q₁ {qConst} {qAny} = (there (there (here (PE.refl , PE.refl)))) ◅ here (PE.refl , PE.refl) ◅ ε 
q₁+q₂≤q₁ {qAny} {qMono} = ε
q₁+q₂≤q₁ {qAny} {qAnti} = ε
q₁+q₂≤q₁ {qAny} {qConst} = ε
q₁+q₂≤q₁ {qAny} {qAny} = ε

q₁+q₂≤q₂ : ∀ {q₁ q₂ : q} → q₂ q≤ (q₁ q+ q₂)
q₁+q₂≤q₂ {qMono} {qMono} = ε
q₁+q₂≤q₂ {qMono} {qAnti} = there (here (PE.refl , PE.refl)) ◅ ε
q₁+q₂≤q₂ {qMono} {qConst} = (there (there (here (PE.refl , PE.refl)))) ◅ ε
q₁+q₂≤q₂ {qMono} {qAny} = ε
q₁+q₂≤q₂ {qAnti} {qMono} = here (PE.refl , PE.refl) ◅ ε
q₁+q₂≤q₂ {qAnti} {qAnti} = ε
q₁+q₂≤q₂ {qAnti} {qConst} = (there (there (there (here (PE.refl , PE.refl))))) ◅ ε
q₁+q₂≤q₂ {qAnti} {qAny} = ε
q₁+q₂≤q₂ {qConst} {qMono} = ε
q₁+q₂≤q₂ {qConst} {qAnti} = ε
q₁+q₂≤q₂ {qConst} {qConst} = ε
q₁+q₂≤q₂ {qConst} {qAny} = ε 
q₁+q₂≤q₂ {qAny} {qMono} = here (PE.refl , PE.refl) ◅ ε
q₁+q₂≤q₂ {qAny} {qAnti} = there (here (PE.refl , PE.refl)) ◅ ε
q₁+q₂≤q₂ {qAny} {qConst} = (there (there (here (PE.refl , PE.refl)))) ◅ here (PE.refl , PE.refl) ◅ ε
q₁+q₂≤q₂ {qAny} {qAny} = ε
