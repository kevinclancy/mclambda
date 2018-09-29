module SemScalars where

open import FinPoset
open import Data.List
open import Data.List.All
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.OrderMorphism renaming (_⇒-Poset_ to _⇒_)
open import Scalars
open import Util

⟦_q⟧ : q → (Poset l0 l0 l0 → Poset l0 l0 l0)
⟦_q⟧ qAny P = P'
  where
    |P| : Set
    |P| = Poset.Carrier P

    ≈-equiv : IsEquivalence (Poset._≈_ P)
    ≈-equiv = IsPartialOrder.isEquivalence (Poset.isPartialOrder P)

    P' : Poset l0 l0 l0
    P' = record
      { Carrier = |P|
      ; _≈_ = Poset._≈_ P
      ; _≤_ = Poset._≈_ P
      ; isPartialOrder = record
        { isPreorder = record 
          { isEquivalence = ≈-equiv
          ; reflexive =  λ {i} {j} i≈j → i≈j
          ; trans = IsEquivalence.trans ≈-equiv 
          }
        ; antisym = λ {i} {j} i≈j j≈i → i≈j 
        }
      }
⟦_q⟧ qMono P = P  
⟦_q⟧ qAnti P = P' 
  where
    open import Relation.Binary
    open Poset using (reflexive ; antisym ; trans)
    
    |P| : Set
    |P| = Poset.Carrier P

    ≈-equivalence : IsEquivalence (Poset._≈_ P)
    ≈-equivalence = IsPartialOrder.isEquivalence (Poset.isPartialOrder P) 

    open IsEquivalence ≈-equivalence renaming (sym to ≈-sym)

    _≤_ : |P| → |P| → Set
    _≤_ = Poset._≤_ P

    _≥_ : |P| → |P| → Set
    p₁ ≥ p₂ = p₂ ≤ p₁
 
    P' : Poset l0 l0 l0
    P' = record 
      { Carrier = |P|
      ; _≈_ = Poset._≈_ P 
      ; _≤_ = _≥_ 
      ; isPartialOrder = record
        { isPreorder = record 
          { isEquivalence = ≈-equivalence
          ; reflexive =  λ {i} {j} i≈j → Poset.reflexive P (≈-sym i≈j) 
          ; trans = λ {i} {j} i≥j j≥k → Poset.trans P j≥k i≥j 
          }
        ; antisym = λ {i} {j} i≥j j≥i → Poset.antisym P j≥i i≥j 
        }
      }
⟦_q⟧ qConst P = ⊤≤-poset
  where
    open import UnitPoset

⟦_q≤_⟧ : (q₁ q₂ : q) → Set₁
⟦ q₁ q≤ q₂ ⟧  = ∀ (P : Poset l0 l0 l0) → (⟦ q₂ q⟧ P) ⇒ (⟦ q₁ q⟧ P)

q≤⟦_⟧ : ∀ {q₁} {q₂} → q₁ q≤ q₂ → ⟦ q₁ q≤ q₂ ⟧
--[[[
q≤⟦_⟧ {q₁} {q₂} q₁≤q₂ = QP.makeInterpretation ⟦_q≤_⟧ (λ {q₁} {q₂} {q₃} → comp {q₁} {q₂} {q₃}) (λ {q} → qRefl {q}) ⟦covers⟧ q₁≤q₂ 
  where
    comp : {q₁ q₂ q₃ : q} → ⟦ q₁ q≤ q₂ ⟧ → ⟦ q₂ q≤ q₃ ⟧ → ⟦ q₁ q≤ q₃ ⟧ 
    comp {q₁} {q₂} {q₃} ⟦q₁≤q₂⟧ ⟦q₂≤q₃⟧ P = (⟦q₁≤q₂⟧ P) ∘ (⟦q₂≤q₃⟧ P)

    qRefl : {q₀ : q} → ⟦ q₀ q≤ q₀ ⟧
    qRefl P = id

    ⟦covers⟧ : All (λ cov → ⟦ (Cover.lo cov) q≤ (Cover.hi cov) ⟧) covers
    ⟦covers⟧ = x1 ∷ x2 ∷ x3 ∷ (λ P → x4 P) ∷ []
      where
        x1 : ⟦ qMono q≤ qAny ⟧
        x1 P = record 
          { fun = λ p → p
          ; monotone = λ {p} {q} p≈q → Poset.reflexive P p≈q
          }

        x2 : ⟦ qAnti q≤ qAny ⟧
        x2 P = record
          { fun = λ p → p
          ; monotone = λ {p} {q} p≈q → Poset.reflexive P (Poset.Eq.sym P p≈q)
          }

        x3 : ⟦ qConst q≤ qMono ⟧
        x3 P = record
          { fun = λ p → tt
          ; monotone = λ {p} {q} p≤q → ε
          }
          where
            open import Data.Unit
            open import Relation.Binary.Closure.ReflexiveTransitive

        x4 : ⟦ qConst q≤ qAnti ⟧
        x4 P = record
          { fun = λ p → tt
          ; monotone = λ {p} {q} p≥q → ε
          }
          where
            open import Data.Unit
            open import Relation.Binary.Closure.ReflexiveTransitive
--]]]
