module SemTyping where

open import Scalars
open import Syntax
open import Kinding
open import Typing
open import Util

open import Relation.Binary

⟦_q⟧ : q → (Poset l0 l0 l0 → Poset l0 l0 l0)
⟦_q⟧ qMono P = P  
⟦_q⟧ qAnti P = P' 
  where
    |P| : Set
    |P| = Poset.Carrier P

    _≤_ : |P| → |P| → Set
    _≤_ = Poset._≤_ P

    _≥_ : |P| → |P| → Set
    p₁ ≥ p₂ = p₂ ≤ p₁
 
    P' : Poset l0 l0 l0
    P' = record 
      { Carrier = |P|
      ; _≈_ = Poset._≈_ P 
      ; _≤_ = {!_≥_!} 
      ; isPartialOrder = record
        { isPreorder = record 
          { isEquivalence = {!!}
          ; reflexive = {!!}
          ; trans = {!!}
          }
        ; antisym = {!!}
        }
      }

-- ⟦_τ⟧ : {n : ℕ} → {Γ : Vec τ n} → {R : Vec q n} → (e₀ : e) → (τ₀ : τ) → (Γ ∣ R ⊢ e₀ ∣ τ₀) → 
      
