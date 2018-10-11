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
qConst q∘ qMono = qMono
qConst q∘ qAnti = qAnti
qConst q∘ qConst = qConst
qConst q∘ qAny = qAny
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

q₁≤q₁+q₂ : ∀ {q₁ q₂ : q} → q₁ q≤ (q₁ q+ q₂)
q₁≤q₁+q₂ {qMono} {qMono} = ε
q₁≤q₁+q₂ {qMono} {qAnti} = here (PE.refl , PE.refl) ◅ ε
q₁≤q₁+q₂ {qMono} {qConst} = ε
q₁≤q₁+q₂ {qMono} {qAny} = here (PE.refl , PE.refl) ◅ ε
q₁≤q₁+q₂ {qAnti} {qMono} = there (here (PE.refl , PE.refl)) ◅ ε
q₁≤q₁+q₂ {qAnti} {qAnti} = ε
q₁≤q₁+q₂ {qAnti} {qConst} = ε
q₁≤q₁+q₂ {qAnti} {qAny} = there (here (PE.refl , PE.refl)) ◅ ε
q₁≤q₁+q₂ {qConst} {qMono} = (there (there (here (PE.refl , PE.refl)))) ◅ ε
q₁≤q₁+q₂ {qConst} {qAnti} = (there (there (there (here (PE.refl , PE.refl))))) ◅ ε
q₁≤q₁+q₂ {qConst} {qConst} = ε
q₁≤q₁+q₂ {qConst} {qAny} = (there (there (here (PE.refl , PE.refl)))) ◅ here (PE.refl , PE.refl) ◅ ε 
q₁≤q₁+q₂ {qAny} {qMono} = ε
q₁≤q₁+q₂ {qAny} {qAnti} = ε
q₁≤q₁+q₂ {qAny} {qConst} = ε
q₁≤q₁+q₂ {qAny} {qAny} = ε

q₂≤q₁+q₂ : ∀ {q₁ q₂ : q} → q₂ q≤ (q₁ q+ q₂)
q₂≤q₁+q₂ {qMono} {qMono} = ε
q₂≤q₁+q₂ {qMono} {qAnti} = there (here (PE.refl , PE.refl)) ◅ ε
q₂≤q₁+q₂ {qMono} {qConst} = (there (there (here (PE.refl , PE.refl)))) ◅ ε
q₂≤q₁+q₂ {qMono} {qAny} = ε
q₂≤q₁+q₂ {qAnti} {qMono} = here (PE.refl , PE.refl) ◅ ε
q₂≤q₁+q₂ {qAnti} {qAnti} = ε
q₂≤q₁+q₂ {qAnti} {qConst} = (there (there (there (here (PE.refl , PE.refl))))) ◅ ε
q₂≤q₁+q₂ {qAnti} {qAny} = ε
q₂≤q₁+q₂ {qConst} {qMono} = ε
q₂≤q₁+q₂ {qConst} {qAnti} = ε
q₂≤q₁+q₂ {qConst} {qConst} = ε
q₂≤q₁+q₂ {qConst} {qAny} = ε 
q₂≤q₁+q₂ {qAny} {qMono} = here (PE.refl , PE.refl) ◅ ε
q₂≤q₁+q₂ {qAny} {qAnti} = there (here (PE.refl , PE.refl)) ◅ ε
q₂≤q₁+q₂ {qAny} {qConst} = (there (there (here (PE.refl , PE.refl)))) ◅ here (PE.refl , PE.refl) ◅ ε
q₂≤q₁+q₂ {qAny} {qAny} = ε


module _ where
  open import Relation.Binary.Closure.ReflexiveTransitive.Properties
  open StarReasoning (_q≺_)

  q≤? : ∀ q → (q q≤ qAny)
  q≤? qMono = begin qMono ⟶⟨ here (PE.refl , PE.refl)  ⟩ qAny ∎
  q≤? qAnti = begin qAnti ⟶⟨ there (here (PE.refl , PE.refl))  ⟩ qAny ∎
  q≤? qConst = begin qConst ⟶⟨ there (there (here (PE.refl , PE.refl))) ⟩ qMono ⟶⟨ here (PE.refl , PE.refl) ⟩ qAny ∎  
  q≤? qAny = begin qAny ∎
