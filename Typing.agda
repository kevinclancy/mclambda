module Typing where

open import Scalars
open import PosetScalars
open import Syntax
open import Kinding

open import Data.Fin as F
open import Data.Nat
open import Data.Vec as V
open import Data.Product
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Nullary

wfτ : Set
wfτ = Σ[ τ₀ ∈ τ ] IsPoset τ₀

data _∣_⊢_∣_ : {n : ℕ} → Vec wfτ n → Vec q n → e → τ → Set

_R+_ : {n : ℕ} → Vec q n → Vec q n → Vec q n
R₁ R+ R₂ = zipWith _q+_ R₁ R₂

_qR∘_ : {n : ℕ} → q → Vec q n → Vec q n
q qR∘ R = V.map (q q∘_) R 

data _∣_⊢_∣_ where
  TyVar : {n k : ℕ} {m : Fin n} {Γ : Vec wfτ n} {R : Vec q n} {τ₀ : τ} {eq1 : τ₀ ≡ proj₁ (V.lookup m Γ)} 
          {eq2 : k ≡ toℕ m} → 
          {eq3 : V.lookup m R ≡ qMono} → {eq4 : ∀ {l : Fin n} → (¬ l ≡ m) → V.lookup l R ≡ qConst} → 
          (Γ ∣ R ⊢ Var k ∣ τ₀)  

  TyBot : {n : ℕ} {Γ : Vec wfτ n} {τ τ₀ : τ} {p : IsSemilat τ τ₀} →
          (Γ ∣ (replicate qConst) ⊢ (Bot τ) ∣ τ)

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
          {τ₁Δ : IsSemilat τ₁ τ₁'} → {τ₂Δ : IsSemilat τ₂ τ₂'} → {wf-τ₁' : IsPoset τ₁'} → 
          (((τ₁' , wf-τ₁') ∷ Γ₀) ∣ (qMono ∷ R₀) ⊢ e₀ ∣ τ₂) → 
          (Γ₀ ∣ R₀ ⊢ e₀ ∣ (τFun τ₁ qMono τ₂))

  TySng : {n : ℕ} → {Γ : Vec wfτ n} → {R₁ R₂ R₃ : Vec q n} → {eKey : e} → {τKey : τ} → {eVal : e} → {τVal : τ} → 
          {τValDelta : τ} → (IsStoset τKey) → (IsSemilat τVal τValDelta) → (R₃ ≡ (qAny qR∘ R₁) R+ R₂) →
          (Γ ∣ R₁ ⊢ eKey ∣ τKey) → (Γ ∣ R₂ ⊢ eVal ∣ τVal) →
          (Γ ∣ R₃ ⊢ (Sng eKey eVal) ∣ (τDict τKey τVal)) 

  TyExtract : {n : ℕ} {q₁ q₂ q₃ : q} → {Γ₀ : Vec wfτ n} → {R₁ R₂ R₃ : Vec q n} → {eDict eBody : e} → {τ σ σ₀ κ κ₀ : τ} →
              (isStosetKey : IsStoset τ) → 
              (isSemilatVal : IsSemilat σ σ₀) → (isSemilatTarget : IsSemilat κ κ₀) → (R₃ ≡ R₁ R+ R₂) → (q₂≤+ : q₂ q≤ qMono) → 
              (q₃≤+ : q₃ q≤ qMono) → (Γ₀ ∣ R₁ ⊢ eDict ∣ (τDict τ σ)) → 
              (((τ , stoset→poset isStosetKey) ∷ (σ , semilat→poset isSemilatVal) ∷ (κ , semilat→poset isSemilatTarget) ∷ Γ₀) ∣ (q₁ ∷ q₂ ∷ q₃ ∷ R₂) ⊢ eBody ∣ κ) →
              (Γ₀ ∣ R₃ ⊢ (Extract eDict eBody) ∣ κ)

  TyPure : {n : ℕ} {Γ₀ : Vec wfτ n} {R₀ : Vec q n} {eBody : e} {τ : τ} → 
           (Γ₀ ∣ R₀ ⊢ eBody ∣ τ) → (Γ₀ ∣ R₀ ⊢ Pure eBody ∣ (τPartial τ))
  
  TyMLet : {n : ℕ} {Γ₀ : Vec wfτ n} {R₁ R₂ R₃ : Vec q n} {eq : R₃ ≡ R₁ R+ R₂} {eFirst eAndThen : e} {τ₁ τ₂ : τ} 
           {τ₁-wf : IsPoset τ₁} → 
           (Γ₀ ∣ R₁ ⊢ eFirst ∣ (τPartial τ₁)) → 
           (((τ₁ , τ₁-wf) ∷ Γ₀) ∣ (qMono ∷ R₂) ⊢ eAndThen ∣ (τPartial τ₂)) → 
           (Γ₀ ∣ R₃ ⊢ MLet eFirst eAndThen ∣ τPartial τ₂)

  TyICell : {n : ℕ} {Γ₀ : Vec wfτ n} {R₀ R₁ : Vec q n} {eq : R₀ ≡ qAny qR∘ R₁} {e₀ : e} {τ₀ : τ} {τ₀-stoset : IsStoset τ₀} → 
            (Γ₀ ∣ R₁  ⊢ e₀ ∣ τ₀) → (Γ₀ ∣ R₀ ⊢ ICell e₀ ∣ τIVar τ₀)

  TyIGet : {n : ℕ} {Γ₀ : Vec wfτ n} {R₁ R₂ R₃ : Vec q n} {eq : R₃ ≡ R₁ R+ R₂} {eCell eBody : e} {τCell τBody τBody' : τ}
           {isCellStoset : IsStoset τCell} {isBodySemilat : IsSemilat τBody τBody'} →
           (Γ₀ ∣ R₁ ⊢ eCell ∣ τIVar τCell) → 
           (((τCell , stoset→poset isCellStoset) ∷ Γ₀) ∣ (qAny ∷ R₂) ⊢ eBody ∣ τBody) →
           (Γ₀ ∣ R₃ ⊢ IGet eCell eBody ∣ τPartial τBody)
  
  TyCapIntro : {n : ℕ} {Γ₀ : Vec wfτ n} {R₁ R₂ : Vec q n} {q₀' : q'} {eq : R₂ ≡ (q'→q q₀') qR∘ R₁}
               {eBody : e} {τ₀ : τ} → (Γ₀ ∣ R₁ ⊢ eBody ∣ τ₀) → (Γ₀ ∣ R₂ ⊢ Cap q₀' eBody ∣ τCapsule q₀' τ₀)

  TyCapElim : {n : ℕ} {Γ₀ : Vec wfτ n} {R₁ R₂ R₃ : Vec q n} {q₀' : q'} {eq : R₃ ≡ R₁ R+ R₂}
              {eCap eBody : e} {τContent τBody : τ} {τContent-wf : IsPoset τContent} → 
              (Γ₀ ∣ R₁ ⊢ eCap ∣ τCapsule q₀' τContent) →
              (((τContent , τContent-wf) ∷ Γ₀) ∣ ((q'→q q₀') ∷ R₂) ⊢ eBody ∣ τBody) →
              (Γ₀ ∣ R₃ ⊢ Uncap q₀' eCap eBody ∣ τBody)

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
τRes-wf (TyHom {τ₁Δ = τ₁Δ} {τ₂Δ = τ₂Δ} τ₁∷Γ@+∷R₀⊢e₀∣τ₂) = FunPoset (semilat→poset τ₁Δ) (semilat→poset τ₂Δ) 
τRes-wf (TySng keyIsStoset valIsSemilat eq d1 d2) = DictPoset keyIsStoset valIsSemilat
τRes-wf (TyExtract _ _ targetIsSemilat _ _ _ _ _) = semilat→poset targetIsSemilat
τRes-wf (TyPure d) = PartialPoset (τRes-wf d)
τRes-wf (TyMLet _ d2) = τRes-wf d2
τRes-wf (TyICell {τ₀-stoset = sto} d) = IVarPoset sto
τRes-wf (TyIGet {isBodySemilat = isBodySemilat} _ _) = PartialPoset (semilat→poset isBodySemilat)
τRes-wf (TyCapIntro {q₀' = q₀'} d) = CapsulePoset q₀' (τRes-wf d)
τRes-wf (TyCapElim _ d2) = τRes-wf d2 
τRes-wf {τRes = τRes} (TyVar  {m = m} {Γ = Γ} {eq1 = PE.refl}) = proj₂ (V.lookup m Γ)   
