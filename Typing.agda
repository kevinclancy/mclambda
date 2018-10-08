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

  TySng : {n : ℕ} → {Γ : Vec wfτ n} → {R₁ R₂ : Vec q n} → {eKey : e} → {τKey : τ} → {eVal : e} → {τVal : τ} → 
          {τValDelta : τ} → (IsStoset τKey) → (IsSemilat τVal τValDelta) →
          (Γ ∣ R₁ ⊢ eKey ∣ τKey) → (Γ ∣ R₂ ⊢ eVal ∣ τVal) →
          (Γ ∣ (qAny qR∘ R₁) R+ R₂ ⊢ (Sng eKey eVal) ∣ (τDict τKey τVal)) 

  TyJoin : {n : ℕ} {Γ : Vec wfτ n} {R₁ : Vec q n} {R₂ : Vec q n} {e₁ e₂ : e} {τ τ₀ : τ} {p : IsSemilat τ τ₀} →
           (Γ ∣ R₁ ⊢ e₁ ∣ τ) → (Γ ∣ R₂ ⊢ e₂ ∣ τ) → (Γ ∣ R₁ R+ R₂ ⊢ (Join τ e₁ e₂) ∣ τ)  
          
  TyAbs : {n : ℕ} {Γ : Vec wfτ n} {R : Vec q n} {q : q} {body : e} {σ τ : τ} {σ-wf : IsPoset σ} → 
          (((σ , σ-wf) ∷ Γ) ∣ (q ∷ R) ⊢ body ∣ τ) → (Γ ∣ R ⊢ (Abs body) ∣ (τFun σ q τ))    

  TyApp : {n : ℕ} {Γ : Vec wfτ n} {R₁ R₂ : Vec q n} {q₀ : q} {e₁ e₂ : e} {σ₀ τ₀ : τ} →
          (Γ ∣ R₁ ⊢ e₁ ∣ τFun σ₀ q₀ τ₀) → (Γ ∣ R₂ ⊢ e₂ ∣ σ₀) → 
          (Γ ∣ (R₁ R+ (q₀ qR∘ R₂)) ⊢ e₂ ∣ τ₀)

  TyPair : {n : ℕ} {Γ : Vec wfτ n} {R₁ : Vec q n} {R₂ : Vec q n} {e₁ e₂ : e} {τ₁ τ₂ : τ} →
           (Γ ∣ R₁ ⊢ e₁ ∣ τ₁) → (Γ ∣ R₂ ⊢ e₂ ∣ τ₂) → (Γ ∣ R₁ R+ R₂ ⊢ (Pair e₁ e₂) ∣ (τProduct τ₁ τ₂))
  
  TyProj1 : {n : ℕ} {Γ : Vec wfτ n} {R : Vec q n} {pair : e} {τ₁ τ₂ : τ} → 
            (Γ ∣ R ⊢ pair ∣ (τProduct τ₁ τ₂)) → (Γ ∣ R ⊢ (Proj1 pair) ∣ τ₁)

  TyProj2 : {n : ℕ} {Γ : Vec wfτ n} {R : Vec q n} {pair : e} {τ₁ τ₂ : τ} → 
            (Γ ∣ R ⊢ pair ∣ (τProduct τ₁ τ₂)) → (Γ ∣ R ⊢ (Proj1 pair) ∣ τ₂)

  TyInl : {n : ℕ} {Γ : Vec wfτ n} {R : Vec q n} {body : e} {τL τR : τ} {τR-wf : IsPoset τR} →
          (Γ ∣ R ⊢ body ∣ τL) → (Γ ∣ R ⊢ Inl τL τR body ∣ τSum τL τR)

  TyInr : {n : ℕ} {Γ : Vec wfτ n} {R : Vec q n} {body : e} {τL τR : τ} {τL-wf : IsPoset τL} →
          (Γ ∣ R ⊢ body ∣ τR) → (Γ ∣ R ⊢ Inr τL τR body ∣ τSum τL τR)

  TyCase : {n : ℕ} {Γ : Vec wfτ n} {R₀ R₁ R₂ : Vec q n} {e₀ e₁ e₂ : e} {τ₁ τ₂ τRes : τ} {τ₁-wf : IsPoset τ₁} 
           {τ₂-wf : IsPoset τ₂} {q₁ q₂ : q} → 
           (Γ ∣ R₀ ⊢ e₀ ∣ τSum τ₁ τ₂) → (((τ₁ , τ₁-wf) ∷ Γ) ∣ (q₁ ∷ R₁) ⊢ e₁ ∣ τRes) → 
           (((τ₂ , τ₂-wf) ∷ Γ) ∣ (q₂ ∷ R₂) ⊢ e₂ ∣ τRes) →
           (Γ ∣ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂)) ⊢ Case e₀ e₁ e₂ ∣ τRes) 
 
  TyHom : {n : ℕ} {Γ₀ : Vec wfτ n} {R₀ : Vec q n} {e₀ : e} {τ₁ τ₁' τ₂ τ₂' : τ} →
          {τ₁⁂ : IsSemilat τ₁ τ₁'} → {τ₂⁂ : IsSemilat τ₂ τ₂'} → {wf-τ₁' : IsPoset τ₁'} → 
          (((τ₁' , wf-τ₁') ∷ Γ₀) ∣ (qMono ∷ R₀) ⊢ e₀ ∣ τ₂) → 
          (Γ₀ ∣ R₀ ⊢ e₀ ∣ (τFun τ₁ qMono τ₂))


τRes-wf :  {n : ℕ} → {Γ₀ : Vec wfτ n} → {R₀ : Vec q n} → {e₀ : e} → {τRes : τ} → (Γ₀ ∣ R₀ ⊢ e₀ ∣ τRes) → (IsPoset τRes) 
τRes-wf (TyBot {p = τRes-semilat}) = semilat→poset τRes-semilat
τRes-wf (TyJoin {_} {_} {R₁} d1 d2) = τRes-wf d1
τRes-wf (TyAbs {τ = τ} {σ-wf = σ-wf} d) = FunPoset σ-wf τ-wf
  where
    τ-wf : IsPoset τ
    τ-wf = τRes-wf d 
τRes-wf (TyApp d₁ d₂) with τRes-wf d₁
τRes-wf (TyApp d₁ d₂) | (FunPoset domPoset codPoset) = codPoset
τRes-wf (TyPair d1 d2) = ProductPoset (τRes-wf d1) (τRes-wf d2)
τRes-wf (TyProj1 d) with τRes-wf d
τRes-wf (TyProj1 d) | ProductPoset wf1 wf2 = wf1
τRes-wf (TyProj2 d) with τRes-wf d
τRes-wf (TyProj2 d) | ProductPoset wf1 wf2 = wf2
τRes-wf (TyInl {τR-wf = τR-wf} d) = SumPoset (τRes-wf d) τR-wf
τRes-wf (TyInr {τL-wf = τL-wf} d) = SumPoset τL-wf (τRes-wf d)
τRes-wf (TyCase _ d _) = τRes-wf d
τRes-wf (TyHom {τ₁⁂ = τ₁⁂} {τ₂⁂ = τ₂⁂} τ₁∷Γ@+∷R₀⊢e₀∣τ₂) = FunPoset (semilat→poset τ₁⁂) (semilat→poset τ₂⁂) 
τRes-wf (TySng keyIsStoset valIsSemilat d1 d2) = DictPoset keyIsStoset valIsSemilat

{-
τRes-wf Γ₀ R₀ .(Inr _ _ _) .(τSum _ _) (TyInr zzz) = {!!}
τRes-wf Γ₀ .(zipWith _q+_ (V.map (_q∘_ (_ q+ _)) _) (zipWith _q+_ _ _)) .(Case _ _ _) τRes (TyCase zzz zzz₁ zzz₂) = {!!}
-}
