module Typing where

open import Scalars
open import Syntax
open import Kinding

open import Data.Nat
open import Data.Vec

-- data IsPoset : τ → Set
-- data IsToset : τ → Set
-- data IsSemilat : τ → τ → Set

data _∣_⊢_∣_ : {n : ℕ} → Vec τ n → Vec q n → e → τ → Set

_R+_ : {n : ℕ} → Vec q n → Vec q n → Vec q n
R₁ R+ R₂ = zipWith _q+_ R₁ R₂

_qR∘_ : {n : ℕ} → q → Vec q n → Vec q n
q qR∘ R = map (q q∘_) R 

data _∣_⊢_∣_ where
  TyBot : {n : ℕ} {Γ : Vec τ n} {τ τ₀ : τ} {p : IsSemilat τ τ₀} →
          (Γ ∣ (replicate qConst) ⊢ (Bot τ) ∣ τ)

  TyExtract : {n : ℕ} (q₁ q₂ q₃ : q) → (Γ : Vec τ n) → (R S : Vec q n) → (eDict eBody : e) → (τ σ σ₀ κ κ₀ : τ) →
              (IsSemilat σ σ₀) → (IsSemilat κ κ₀) → (q₂ q≤ qMono) → (q₃ q≤ qMono) → 
              (Γ ∣ R ⊢ eDict ∣ (τDict τ σ)) → ((κ ∷ σ ∷ τ ∷ Γ) ∣ (q₃ ∷ q₂ ∷ q₁ ∷ S) ⊢ eBody ∣ κ) →
              (Γ ∣ (R R+ S) ⊢ (Extract eDict eBody) ∣ κ)

  TyCons : {n : ℕ} → (Γ : Vec τ n) → (R S T : Vec q n) → (eKey : e) → (τKey : τ) → (eVal : e) → (τVal : τ) → 
           (τValDelta : τ) → (eDict : e) → (IsToset τKey) → (IsSemilat τVal τValDelta) →
           (Γ ∣ R ⊢ eKey ∣ τKey) → (Γ ∣ S ⊢ eVal ∣ τVal) → (Γ ∣ T ⊢ eDict ∣ (τDict τKey τVal)) →
           (Γ ∣ ((qAny qR∘ R) R+ S) R+ T ⊢ (Cons eKey eVal eDict) ∣ (τDict τKey τVal)) 

  TyJoin : {n : ℕ} {Γ : Vec τ n} {R : Vec q n} {e₁ e₂ : e} {τ τ₀ : τ} {p : IsSemilat τ τ₀} →
           (Γ ∣ R ⊢ e₁ ∣ τ) → (Γ ∣ R ⊢ e₂ ∣ τ) → (Γ ∣ R ⊢ (Join τ e₁ e₂) ∣ τ)  
          
  TyAbs : {n : ℕ} {Γ : Vec τ n} {R : Vec q n} {q : q} {body : e} {σ τ : τ} → 
          ((σ ∷ Γ) ∣ (q ∷ R) ⊢ body ∣ τ) → (Γ ∣ R ⊢ (Abs body) ∣ (τFun σ q τ))    

  
