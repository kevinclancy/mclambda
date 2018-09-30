module SemScalars where

open import Function using (_$_)
open import Data.Unit hiding (_≤_)
open import Data.List
open import Data.List.All
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.OrderMorphism renaming (_⇒-Poset_ to _⇒_)

open import FinPoset
open import Scalars
open import Util
open import UnitPoset


⟦_q⟧ : q → (Poset l0 l0 l0 → Poset l0 l0 l0)
--[[[
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
--]]]

-- the functor ⟦ q₀ q⟧'s arrow mapping
⟦_q⇒⟧ : (q₀ : q) → (∀ {P Q : Poset l0 l0 l0} → (P ⇒ Q) → ((⟦ q₀ q⟧ P) ⇒ ⟦ q₀ q⟧ Q))
--[[[
⟦ qMono q⇒⟧ {P} {Q} f = 
  record
  { fun = λ p → |f| p 
  ; monotone = |f|-monotone 
  } 
  where
    |f| = _⇒_.fun f
    |f|-monotone = _⇒_.monotone f
⟦ qAnti q⇒⟧ {P} {Q} f =
  record
  { fun = λ p → |f| p 
  ; monotone = |f|-monotone 
  } 
  where
    |f| = _⇒_.fun f
    |f|-monotone = _⇒_.monotone f
⟦ qConst q⇒⟧ {P} {Q} f =
  record
  { fun = λ p → tt
  ; monotone = λ {x} {y} x≤y → x≤y 
  } 
  where
    open import Data.Unit
    |f| = _⇒_.fun f
    |f|-monotone = _⇒_.monotone f
⟦ qAny q⇒⟧ {P} {Q} f =
  record
  { fun = fun
  ; monotone = monotone 
  } 
  where
    open import Function using (_$_)

    |f| = _⇒_.fun f
    |f|-monotone = _⇒_.monotone f

    fun : (Poset.Carrier $ ⟦ qAny q⟧ P) → (Poset.Carrier $ ⟦ qAny q⟧ Q)
    fun p = |f| p 

    monotone : (Poset._≈_ $ ⟦ qAny q⟧ P) =[ fun ]⇒ (Poset._≈_ $ ⟦ qAny q⟧ Q)
    monotone {p₁} {p₂} p₁≈p₂ = Poset.antisym Q fp₁≤fp₂ fp₂≤fp₁ 
      where
        fp₁≤fp₂ : Poset._≤_ Q (|f| p₁) (|f| p₂)
        fp₁≤fp₂ = |f|-monotone (Poset.reflexive P p₁≈p₂)
 
        fp₂≤fp₁ : Poset._≤_ Q (|f| p₂) (|f| p₁)
        fp₂≤fp₁ = |f|-monotone (Poset.reflexive P (Poset.Eq.sym P p₁≈p₂))
--]]]

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

q-cartesian⃗ : (P Q : Poset l0 l0 l0) → (t₀ : q) → (⟦ t₀ q⟧ $ ×-poset P Q) ⇒ (×-poset (⟦ t₀ q⟧ P) (⟦ t₀ q⟧ Q))
--[[[
q-cartesian⃗ P Q qAny = 
  record
  { fun = λ x → x
  ; monotone = λ x≈y → x≈y
  }
q-cartesian⃗ P Q qMono = 
  record
  { fun = λ x → x
  ; monotone = λ x≤y → x≤y
  }
q-cartesian⃗ P Q qAnti = 
  record
  { fun = λ x → x
  ; monotone = λ x≤y → x≤y
  }
q-cartesian⃗ P Q qConst =
  record
  { fun = λ _ → (tt , tt)
  ; monotone = λ _ → (Poset.refl ⊤≤-poset , Poset.refl ⊤≤-poset) 
  }
--]]]

q-cartesian⃖ : (P Q : Poset l0 l0 l0) → (t₀ : q) → (×-poset (⟦ t₀ q⟧ P) (⟦ t₀ q⟧ Q)) ⇒ (⟦ t₀ q⟧ $ ×-poset P Q)
--[[[
q-cartesian⃖ P Q qAny =
  record
  { fun = λ x → x
  ; monotone = λ x≈y → x≈y
  }
q-cartesian⃖ P Q qMono =
  record
  { fun = λ x → x
  ; monotone = λ x≤y → x≤y
  }
q-cartesian⃖ P Q qAnti =
  record
  { fun = λ x → x
  ; monotone = λ x≤y → x≤y
  }
q-cartesian⃖ P Q qConst =
  record
  { fun = λ _ → tt
  ; monotone = λ _ → Poset.refl ⊤≤-poset 
  }
--]]]

-- comultiplication
δ : (t₁ t₂ : q) → (P : Poset l0 l0 l0) → (⟦ t₁ q∘ t₂ q⟧ P) ⇒ (⟦ t₁ q⟧ $ ⟦ t₂ q⟧ P)
--[[[
δ qMono qMono P = id
δ qMono qAnti P = id
δ qMono qConst P = id
δ qMono qAny P = id
δ qAnti qMono P = id
δ qAnti qAnti P =
  record
  { fun = λ x → x
  ; monotone = λ {x} {y} x≤y → x≤y
  }
δ qAnti qConst P =
  record
  { fun = λ x → x
  ; monotone = λ {x} {y} x≤y → x≤y
  }
δ qAnti qAny P =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Poset.Carrier $ ⟦ qAny q⟧ P) → (Poset.Carrier $ ⟦ qAnti q⟧ $ ⟦ qAny q⟧ P) 
    fun x = x

    monotone : (Poset._≤_ $ ⟦ qAny q⟧ P) =[ fun ]⇒ (Poset._≤_ $ ⟦ qAnti q⟧ $ ⟦ qAny q⟧ P) 
    monotone {x} {y} x≈y = Poset.Eq.sym (⟦ qAny q⟧ P) x≈y
δ qConst qMono P = id
δ qConst qAnti P = id
δ qConst qConst P = id
δ qConst qAny P = id
δ qAny qMono P = id
δ qAny qAnti P = id
δ qAny qConst P = 
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Poset.Carrier $ ⟦ qConst q⟧ P) → (Poset.Carrier $ ⟦ qAny q⟧ $ ⟦ qConst q⟧ P) 
    fun x = tt

    monotone : (Poset._≤_ $ ⟦ qConst q⟧ P) =[ fun ]⇒ (Poset._≤_ $ ⟦ qAny q⟧ $ ⟦ qConst q⟧ P) 
    monotone {x} {y} x≤y = Poset.refl (⟦ qAny q⟧ $ ⟦ qConst q⟧ P)
δ qAny qAny P = id
--]]]

δ⁻¹ : (t₁ t₂ : q) → (P : Poset l0 l0 l0) → (⟦ t₁ q⟧ $ ⟦ t₂ q⟧ P) ⇒ (⟦ t₁ q∘ t₂ q⟧ P) 
--[[[
δ⁻¹ qMono qMono P = id
δ⁻¹ qMono qAnti P = id
δ⁻¹ qMono qConst P = id
δ⁻¹ qMono qAny P = id
δ⁻¹ qAnti qMono P = id
δ⁻¹ qAnti qAnti P =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Poset.Carrier $ ⟦ qAnti q⟧ $ ⟦ qAnti q⟧ P) → (Poset.Carrier $ ⟦ qMono q⟧ P)
    fun x = x

    monotone : (Poset._≤_ $ ⟦ qAnti q⟧ $ ⟦ qAnti q⟧ P) =[ fun ]⇒ (Poset._≤_ $ ⟦ qMono q⟧ P)
    monotone {x} {y} x≤y = x≤y
δ⁻¹ qAnti qConst P = 
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Poset.Carrier $ ⟦ qAnti q⟧ $ ⟦ qConst q⟧ P) → (Poset.Carrier $ ⟦ qConst q⟧ P)
    fun x = tt

    monotone : (Poset._≤_ $ ⟦ qAnti q⟧ $ ⟦ qConst q⟧ P) =[ fun ]⇒ (Poset._≤_ $ ⟦ qConst q⟧ P)
    monotone {x} {y} x≤y = Poset.refl (⟦ qConst q⟧ P)
δ⁻¹ qAnti qAny P = 
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Poset.Carrier $ ⟦ qAnti q⟧ $ ⟦ qAny q⟧ P) → (Poset.Carrier $ ⟦ qAny q⟧ P)
    fun x = x

    monotone : (Poset._≤_ $ ⟦ qAnti q⟧ $ ⟦ qAny q⟧ P) =[ fun ]⇒ (Poset._≤_ $ ⟦ qAny q⟧ P)
    monotone {x} {y} x≈y = Poset.Eq.sym (⟦ qAny q⟧ P) x≈y
δ⁻¹ qConst qMono P = id
δ⁻¹ qConst qAnti P = id
δ⁻¹ qConst qConst P = id
δ⁻¹ qConst qAny P = id
δ⁻¹ qAny qMono P = id
δ⁻¹ qAny qAnti P = id
δ⁻¹ qAny qConst P =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Poset.Carrier $ ⟦ qAny q⟧ $ ⟦ qConst q⟧ P) → (Poset.Carrier $ ⟦ qConst q⟧ P)
    fun x = tt

    monotone : (Poset._≤_ $ ⟦ qAny q⟧ $ ⟦ qConst q⟧ P) =[ fun ]⇒ (Poset._≤_ $ ⟦ qConst q⟧ P)
    monotone {x} {y} x≤y = Poset.refl (⟦ qConst q⟧ P)
δ⁻¹ qAny qAny P = id
--]]]

