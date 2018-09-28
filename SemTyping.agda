module SemTyping where

open import Scalars
open import Syntax
open import Kinding
open import Typing
open import Util
open import SemPoset
open import Data.Product
open import Data.Vec.Relation.Pointwise.Inductive as VPW
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.OrderMorphism renaming (_⇒-Poset_ to _⇒_)
open import Relation.Binary.PropositionalEquality as PE

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

open import Data.Nat
open import Data.Vec

⟦_Γ∣_R⟧ : {n : ℕ} → (Γ : Vec wfτ n) → (R : Vec q n) → Poset l0 l0 l0
⟦ []  Γ∣ [] R⟧ = ⊤≤-poset
  where
    open import UnitPoset
⟦ (τ₀ , poset-τ₀) ∷ Γ₀  Γ∣ q₀ ∷ R₀ R⟧ = ×-poset first rest
  where
    open import Data.Product.Relation.Pointwise.NonDependent

    rest : Poset l0 l0 l0
    rest = ⟦ Γ₀ Γ∣ R₀ R⟧

    first : Poset l0 l0 l0
    first = ⟦ q₀ q⟧ ⟦ poset-τ₀ ⁎⟧ 


strengthen : (τ₀ : wfτ) → (q₀ q₀' : q) → (q₀ q≤ q₀') → (⟦ q₀ q⟧ ⟦ proj₂ τ₀ ⁎⟧ ⇒ ⟦ q₀' q⟧ ⟦ proj₂ τ₀ ⁎⟧)
strengthen τ₀ q₀ .q₀ .Relation.Binary.Closure.ReflexiveTransitive.Star.ε = ?
strengthen τ₀ q₀ q₀' (x .Relation.Binary.Closure.ReflexiveTransitive.Star.◅ q₀≤q₀') = ?

strengthenR : {n : ℕ} → (Γ₀ : Vec wfτ n) → (R₀ : Vec q n) → (R₀' : Vec q n) → (VPW.Pointwise _q≤_ R₀ R₀') → 
              (⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₀' R⟧)
strengthenR {n} Γ₀ R₀ R₀' R₀≤R₀' = {!!}

⟦_⊢⟧ : {n : ℕ} → {Γ₀ : Vec wfτ n} → {R₀ : Vec q n} → {e₀ : e} → {τ₀ : τ} → {τ₀-wf : IsPoset τ₀} → 
       (x : Γ₀ ∣ R₀ ⊢ e₀ ∣ τ₀) → ⟦ Γ₀ Γ∣ R₀ R⟧  ⇒ ⟦ τ₀-wf ⁎⟧ 
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyBot {n} {Γ} {τ₀} {τ₀'} {τ₀-semilat}) = record
  { fun = λ _ → ⊥'
  ; monotone = λ {_} {_} _ → codP.refl
  }
  where
    open import SemSemilat
    open import Relation.Binary.Lattice
    open SemSemilat.SemSemilat ⟦ τ₀-semilat ⁂⟧
    open BoundedJoinSemilattice S
    module codP = IsPartialOrder (Poset.isPartialOrder ⟦ τ₀-wf ⁎⟧)

    isPosetEq : τ₀-wf ≡ (semilat→poset τ₀-semilat)
    isPosetEq = isPosetUnique (τ₀-wf) (semilat→poset τ₀-semilat)

    ⊥' : Poset.Carrier ⟦ τ₀-wf ⁎⟧
    ⊥' rewrite (PE.cong (λ · → Poset.Carrier ⟦ · ⁎⟧) isPosetEq) | (PE.sym US) = ⊥

⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyJoin {n} {Γ₀} {R₁} {R₂} {e₁} {e₂} {τ₀} {τ₀'} {τ₀-semilat} Γ∣R₁⊢e₁∣τ₀ Γ∣R₂⊢e₂∣τ₀) = record
  { fun = {!!}
  ; monotone = {!!}
  }
  where
    open import SemSemilat
    open import Relation.Binary.Lattice
    open SemSemilat.SemSemilat ⟦ τ₀-semilat ⁂⟧
    open BoundedJoinSemilattice S
    module codP = IsPartialOrder (Poset.isPartialOrder ⟦ τ₀-wf ⁎⟧)

    f₁ : ⟦ Γ₀ Γ∣ R₁ R⟧ ⇒ ⟦ τ₀-wf ⁎⟧ 
    f₁ = ⟦_⊢⟧ {n} {Γ₀} {R₁} {e₁} {τ₀} {τ₀-wf} Γ∣R₁⊢e₁∣τ₀

    f₂ : ⟦ Γ₀ Γ∣ R₂ R⟧ ⇒ ⟦ τ₀-wf ⁎⟧
    f₂ = ⟦_⊢⟧ {n} {Γ₀} {R₂} {e₂} {τ₀} {τ₀-wf} Γ∣R₂⊢e₂∣τ₀
