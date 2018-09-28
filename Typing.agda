module Typing where

open import Scalars
open import Syntax
open import Kinding

open import Data.Nat
open import Data.Vec as V
open import Data.Product

-- data IsPoset : τ → Set
-- data IsToset : τ → Set
-- data IsSemilat : τ → τ → Set

wfτ : Set
wfτ = Σ[ τ₀ ∈ τ ] IsPoset τ₀

data _∣_⊢_∣_ : {n : ℕ} → Vec wfτ n → Vec q n → e → τ → Set

_R+_ : {n : ℕ} → Vec q n → Vec q n → Vec q n
R₁ R+ R₂ = zipWith _q+_ R₁ R₂

_qR∘_ : {n : ℕ} → q → Vec q n → Vec q n
q qR∘ R = V.map (q q∘_) R 

data _∣_⊢_∣_ where
  TyBot : {n : ℕ} {Γ : Vec wfτ n} {τ τ₀ : τ} {p : IsSemilat τ τ₀} →
          (Γ ∣ (replicate qConst) ⊢ (Bot τ) ∣ τ)

--  TyExtract : {n : ℕ} (q₁ q₂ q₃ : q) → (Γ : Vec τ n) → (R S : Vec q n) → (eDict eBody : e) → (τ σ σ₀ κ κ₀ : τ) →
--              (IsSemilat σ σ₀) → (IsSemilat κ κ₀) → (q₂ q≤ qMono) → (q₃ q≤ qMono) → 
--              (Γ ∣ R ⊢ eDict ∣ (τDict τ σ)) → ((κ ∷ σ ∷ τ ∷ Γ) ∣ (q₃ ∷ q₂ ∷ q₁ ∷ S) ⊢ eBody ∣ κ) →
--              (Γ ∣ (R R+ S) ⊢ (Extract eDict eBody) ∣ κ)

--  TyCons : {n : ℕ} → (Γ : Vec τ n) → (R S T : Vec q n) → (eKey : e) → (τKey : τ) → (eVal : e) → (τVal : τ) → 
--           (τValDelta : τ) → (eDict : e) → (IsToset τKey) → (IsSemilat τVal τValDelta) →
--           (Γ ∣ R ⊢ eKey ∣ τKey) → (Γ ∣ S ⊢ eVal ∣ τVal) → (Γ ∣ T ⊢ eDict ∣ (τDict τKey τVal)) →
--           (Γ ∣ ((qAny qR∘ R) R+ S) R+ T ⊢ (Cons eKey eVal eDict) ∣ (τDict τKey τVal)) 

  TyJoin : {n : ℕ} {Γ : Vec wfτ n} {R₁ : Vec q n} {R₂ : Vec q n} {e₁ e₂ : e} {τ τ₀ : τ} {p : IsSemilat τ τ₀} →
           (Γ ∣ R₁ ⊢ e₁ ∣ τ) → (Γ ∣ R₂ ⊢ e₂ ∣ τ) → (Γ ∣ R₁ R+ R₂ ⊢ (Join τ e₁ e₂) ∣ τ)  
          
  TyAbs : {n : ℕ} {Γ : Vec wfτ n} {R : Vec q n} {q : q} {body : e} {σ τ : τ} {σ-wf : IsPoset σ} → 
          (((σ , σ-wf) ∷ Γ) ∣ (q ∷ R) ⊢ body ∣ τ) → (Γ ∣ R ⊢ (Abs body) ∣ (τFun σ q τ))    

  TyPair : {n : ℕ} {Γ : Vec wfτ n} {R₁ : Vec q n} {R₂ : Vec q n} {e₁ e₂ : e} {τ₁ τ₂ : τ} →
           (Γ ∣ R₁ ⊢ e₁ ∣ τ₁) → (Γ ∣ R₂ ⊢ e₂ ∣ τ₂) → (Γ ∣ R₁ R+ R₂ ⊢ (Pair e₁ e₂) ∣ (τProduct τ₁ τ₂))
  
  TyProj1 : {n : ℕ} {Γ : Vec wfτ n} {R : Vec q n} {pair : e} {τ₁ τ₂ : τ} → 
            (Γ ∣ R ⊢ pair ∣ (τProduct τ₁ τ₂)) → (Γ ∣ R ⊢ (Proj1 pair) ∣ τ₁)

  TyProj2 : {n : ℕ} {Γ : Vec wfτ n} {R : Vec q n} {pair : e} {τ₁ τ₂ : τ} → 
            (Γ ∣ R ⊢ pair ∣ (τProduct τ₁ τ₂)) → (Γ ∣ R ⊢ (Proj1 pair) ∣ τ₁)

  TyInl : {n : ℕ} {Γ : Vec wfτ n} {R : Vec q n} {body : e} {τL τR : τ} →
          (Γ ∣ R ⊢ body ∣ τL) → (Γ ∣ R ⊢ Inl τL τR body ∣ τSum τL τR)

  TyInr : {n : ℕ} {Γ : Vec wfτ n} {R : Vec q n} {body : e} {τL τR : τ} →
          (Γ ∣ R ⊢ body ∣ τR) → (Γ ∣ R ⊢ Inr τL τR body ∣ τSum τL τR)

  TyCase : {n : ℕ} {Γ : Vec wfτ n} {R₀ R₁ R₂ : Vec q n} {e₀ e₁ e₂ : e} {τ₁ τ₂ τRes : τ} {τ₁-wf : IsPoset τ₁} 
           {τ₂-wf : IsPoset τ₂} {q₁ q₂ : q} → 
           (Γ ∣ R₀ ⊢ e₀ ∣ τSum τ₁ τ₂) → (((τ₁ , τ₁-wf) ∷ Γ) ∣ (q₁ ∷ R₁) ⊢ e₁ ∣ τRes) → 
           (((τ₂ , τ₂-wf) ∷ Γ) ∣ (q₂ ∷ R₂) ⊢ e₂ ∣ τRes) →
           (Γ ∣ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂)) ⊢ Case e₀ e₁ e₂ ∣ τRes) 

 
