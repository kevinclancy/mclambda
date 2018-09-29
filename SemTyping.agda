module SemTyping where

open import Scalars
open import Syntax
open import Kinding
open import Typing
open import Util
open import SemPoset
open import FinPoset

open import Data.Vec
open import Data.Nat hiding (_≤_ ; _≥_)  
open import Data.Product
open import Data.Vec.Relation.Pointwise.Inductive as VPW
open import Data.List.All
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.OrderMorphism renaming (_⇒-Poset_ to _⇒_)
open import Relation.Binary.PropositionalEquality as PE
open import Posets
open import SemScalars

_R≤_ : {n : ℕ} → (Vec q n) → (Vec q n) → Set
R₁ R≤ R₂ = VPW.Pointwise _q≤_ R₁ R₂

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

strengthenR : {n : ℕ} → (Γ₀ : Vec wfτ n) → (R₀ : Vec q n) → (R₀' : Vec q n) → (VPW.Pointwise _q≤_ R₀' R₀) → 
              (⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₀' R⟧)
strengthenR {.0} Γ₀ .[] .[] [] = record
  { fun = λ x → x
  ; monotone = λ {x} {y} x≤y → x≤y
  }
strengthenR {(suc n')} (wfτ ∷ Γ₀') (q₀ ∷ R₀) (q₀' ∷ R₀') (q₀≤q₀' ∷ R₀≤R₀') = 
  (q≤⟦ q₀≤q₀' ⟧ ⟦ proj₂ wfτ ⁎⟧) ⟨×⟩ (strengthenR Γ₀' R₀ R₀' R₀≤R₀')  

⟦_⊢⟧ : {n : ℕ} → {Γ₀ : Vec wfτ n} → {R₀ : Vec q n} → {e₀ : e} → {τ₀ : τ} → {τ₀-wf : IsPoset τ₀} → 
       (x : Γ₀ ∣ R₀ ⊢ e₀ ∣ τ₀) → ⟦ Γ₀ Γ∣ R₀ R⟧  ⇒ ⟦ τ₀-wf ⁎⟧ 
--[[[
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyBot {n} {Γ} {τ₀} {τ₀'} {τ₀-semilat}) = 
  --[[[
  record
  { fun = λ _ → ⊥'
  ; monotone = λ {_} {_} _ → codP.refl
  }
  where
    open import SemSemilat
    open import Relation.Binary.Lattice
    open SemSemilat.SemSemilat ⟦ τ₀-semilat ⁂⟧
    open BoundedJoinSemilattice S

    module codP = Poset ⟦ τ₀-wf ⁎⟧ 

    isPosetEq : τ₀-wf ≡ (semilat→poset τ₀-semilat)
    isPosetEq = isPosetUnique (τ₀-wf) (semilat→poset τ₀-semilat)

    ⊥' : Poset.Carrier ⟦ τ₀-wf ⁎⟧
    ⊥' rewrite (PE.cong (λ · → Poset.Carrier ⟦ · ⁎⟧) isPosetEq) | (PE.sym US) = ⊥
  --]]]
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyJoin {n} {Γ₀} {R₁} {R₂} {e₁} {e₂} {τ₀} {τ₀'} {τ₀-semilat} Γ∣R₁⊢e₁∣τ₀ Γ∣R₂⊢e₂∣τ₀) = 
  --[[[
  ⟨ wk1 , wk2 ⟩ >> (f₁ ⟨×⟩ f₂) >> _∨'_
  where
    open import SemSemilat
    open import Relation.Binary.Lattice
    open import Data.Product.Relation.Pointwise.NonDependent
    open SemSemilat.SemSemilat ⟦ τ₀-semilat ⁂⟧
    open BoundedJoinSemilattice S
    module codP = IsPartialOrder (Poset.isPartialOrder ⟦ τ₀-wf ⁎⟧)

    R₁≤R₁+R₂ : R₁ R≤ (R₁ R+ R₂)
    R₁≤R₁+R₂ = R₁≤R₁+R₂' {n} R₁ R₂
      where
        R₁≤R₁+R₂' : {n : ℕ} → (R₁ R₂ : Vec q n) → R₁ R≤ (R₁ R+ R₂)
        R₁≤R₁+R₂' (q₁ ∷ R₁) (q₂ ∷ R₂) = q₁+q₂≤q₁ ∷ (R₁≤R₁+R₂' R₁ R₂)
        R₁≤R₁+R₂' [] [] = []
    
    R₂≤R₁+R₂ : R₂ R≤ (R₁ R+ R₂)  
    R₂≤R₁+R₂ = R₂≤R₁+R₂' R₁ R₂ 
      where
        R₂≤R₁+R₂' : {n : ℕ} → (R₁ R₂ : Vec q n) → R₂ R≤ (R₁ R+ R₂)
        R₂≤R₁+R₂' (q₁ ∷ R₁) (q₂ ∷ R₂) = q₁+q₂≤q₂ ∷ (R₂≤R₁+R₂' R₁ R₂)
        R₂≤R₁+R₂' [] [] = []

    wk1 : ⟦ Γ₀ Γ∣ R₁ R+ R₂ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₁ R⟧
    wk1 = strengthenR Γ₀ (R₁ R+ R₂) R₁ R₁≤R₁+R₂

    wk2 : ⟦ Γ₀ Γ∣ R₁ R+ R₂ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₂ R⟧
    wk2 = strengthenR Γ₀ (R₁ R+ R₂) R₂ R₂≤R₁+R₂

    f₁ : ⟦ Γ₀ Γ∣ R₁ R⟧ ⇒ ⟦ τ₀-wf ⁎⟧ 
    f₁ = ⟦_⊢⟧ {n} {Γ₀} {R₁} {e₁} {τ₀} {τ₀-wf} Γ∣R₁⊢e₁∣τ₀
    
    f₂ : ⟦ Γ₀ Γ∣ R₂ R⟧ ⇒ ⟦ τ₀-wf ⁎⟧
    f₂ = ⟦_⊢⟧ {n} {Γ₀} {R₂} {e₂} {τ₀} {τ₀-wf} Γ∣R₂⊢e₂∣τ₀

    _∨'_ : (×-poset ⟦ τ₀-wf ⁎⟧ ⟦ τ₀-wf ⁎⟧) ⇒ ⟦ τ₀-wf ⁎⟧
    _∨'_ rewrite (isPosetUnique τ₀-wf (semilat→poset τ₀-semilat)) | PE.sym US = record
      { fun = fun
      ; monotone = monotone
      }
      where  
        fun : Carrier × Carrier → Carrier
        fun (p₁ , p₂) = p₁ ∨ p₂ 

        monotone : (Poset._≤_ (×-poset poset poset)) =[ fun ]⇒ (Poset._≤_ poset)
        monotone {x} {y} (x₁≤y₁ , x₂≤y₂) = ∨-monotonic (BoundedJoinSemilattice.joinSemiLattice S) x₁≤y₁ x₂≤y₂
          where
            open import Relation.Binary.Properties.JoinSemilattice

  --]]]
⟦_⊢⟧ {τ₀-wf = FunPoset domPoset codPoset} (TyAbs {n} {Γ₀} {R₀} {q₁} {body} {σ₁} {τ₁} {σ₁-wf} (σ₁∷Γ∣q₁∷R⊢body∣τ₁)) 
  with τRes-wf σ₁∷Γ∣q₁∷R⊢body∣τ₁ 
⟦_⊢⟧ {τ₀-wf = FunPoset domPoset codPoset} (TyAbs {n} {Γ₀} {R₀} {q₁} {body} {σ₁} {τ₁} {σ₁-wf} (σ₁∷Γ∣q₁∷R⊢body∣τ₁)) | τ₁-wf 
  rewrite isPosetUnique codPoset τ₁-wf | isPosetUnique domPoset σ₁-wf =
  Λ ⟦σ₁∷Γ∣q₁∷R⟧⇒⟦τ₁⟧ 
  where
    ⟦σ₁∷Γ∣q₁∷R⟧⇒⟦τ₁⟧ : ⟦ (σ₁ , σ₁-wf) ∷ Γ₀ Γ∣ q₁ ∷ R₀ R⟧ ⇒ ⟦ τ₁-wf ⁎⟧
    ⟦σ₁∷Γ∣q₁∷R⟧⇒⟦τ₁⟧ = ⟦_⊢⟧ {τ₀-wf = τ₁-wf} σ₁∷Γ∣q₁∷R⊢body∣τ₁ 
⟦_⊢⟧ {τ₀-wf = ProductPoset posetL posetR} (TyPair {n} {Γ₀} {R₁} {R₂} {e₁} {e₂} {τ₁} {τ₂} Γ₀∣R₁⊢e₁∣τ₁ Γ₀∣R₂⊢e₂∣τ₂)
  with τ₁-wf | τ₂-wf | τ₁-wf≡posetL | τ₂-wf≡posetR
  where
    τ₁-wf : IsPoset τ₁
    τ₁-wf = τRes-wf Γ₀∣R₁⊢e₁∣τ₁

    τ₂-wf : IsPoset τ₂
    τ₂-wf = τRes-wf Γ₀∣R₂⊢e₂∣τ₂

    τ₁-wf≡posetL : τ₁-wf ≡ posetL
    τ₁-wf≡posetL = isPosetUnique τ₁-wf posetL

    τ₂-wf≡posetR : τ₂-wf ≡ posetR
    τ₂-wf≡posetR = isPosetUnique τ₂-wf posetR    
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyPair {n} {Γ₀} {R₁} {R₂} {e₁} {e₂} {τ₁} {τ₂} Γ₀∣R₁⊢e₁∣τ₁ Γ₀∣R₂⊢e₂∣τ₂)
  | τ₁-wf | τ₂-wf | PE.refl | PE.refl =
  ⟨ wk1 , wk2 ⟩ >> (⟦Γ₀∣R₁⊢e₁∣τ₁⟧ ⟨×⟩ ⟦Γ₀∣R₂⊢e₂∣τ₂⟧) 
  where 
    R₁≤R₁+R₂ : R₁ R≤ (R₁ R+ R₂)
    R₁≤R₁+R₂ = R₁≤R₁+R₂' {n} R₁ R₂
      where
        R₁≤R₁+R₂' : {n : ℕ} → (R₁ R₂ : Vec q n) → R₁ R≤ (R₁ R+ R₂)
        R₁≤R₁+R₂' (q₁ ∷ R₁) (q₂ ∷ R₂) = q₁+q₂≤q₁ ∷ (R₁≤R₁+R₂' R₁ R₂)
        R₁≤R₁+R₂' [] [] = []
    
    R₂≤R₁+R₂ : R₂ R≤ (R₁ R+ R₂)  
    R₂≤R₁+R₂ = R₂≤R₁+R₂' R₁ R₂ 
      where
        R₂≤R₁+R₂' : {n : ℕ} → (R₁ R₂ : Vec q n) → R₂ R≤ (R₁ R+ R₂)
        R₂≤R₁+R₂' (q₁ ∷ R₁) (q₂ ∷ R₂) = q₁+q₂≤q₂ ∷ (R₂≤R₁+R₂' R₁ R₂)
        R₂≤R₁+R₂' [] [] = []

    wk1 : ⟦ Γ₀ Γ∣ R₁ R+ R₂ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₁ R⟧
    wk1 = strengthenR Γ₀ (R₁ R+ R₂) R₁ R₁≤R₁+R₂

    wk2 : ⟦ Γ₀ Γ∣ R₁ R+ R₂ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₂ R⟧
    wk2 = strengthenR Γ₀ (R₁ R+ R₂) R₂ R₂≤R₁+R₂    
  
    ⟦Γ₀∣R₁⊢e₁∣τ₁⟧ : ⟦ Γ₀ Γ∣ R₁ R⟧ ⇒ ⟦ τ₁-wf ⁎⟧ 
    ⟦Γ₀∣R₁⊢e₁∣τ₁⟧ = ⟦_⊢⟧ {τ₀-wf = τ₁-wf} Γ₀∣R₁⊢e₁∣τ₁   

    ⟦Γ₀∣R₂⊢e₂∣τ₂⟧ : ⟦ Γ₀ Γ∣ R₂ R⟧ ⇒ ⟦ τ₂-wf ⁎⟧
    ⟦Γ₀∣R₂⊢e₂∣τ₂⟧ = ⟦_⊢⟧ {τ₀-wf = τ₂-wf} Γ₀∣R₂⊢e₂∣τ₂   
--]]]
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyProj1 {n} {Γ₀} {R₀} {ePair} {τ₁} {τ₂} Γ₀∣R₀⊢ePair∣τ₁×τ₂) = 
  ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ >> π₁ {⟦ τ₀-wf ⁎⟧} {⟦ τ₂-wf ⁎⟧}
  where
    τ₁×τ₂-wf : IsPoset (τProduct τ₁ τ₂)
    τ₁×τ₂-wf = τRes-wf Γ₀∣R₀⊢ePair∣τ₁×τ₂

    τ₁-wf : IsPoset τ₁
    τ₁-wf with τ₁×τ₂-wf
    τ₁-wf | ProductPoset goal _ = goal

    τ₂-wf : IsPoset τ₂
    τ₂-wf with τ₁×τ₂-wf
    τ₂-wf | ProductPoset _ goal = goal

    ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ : ⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ ⟦ ProductPoset τ₀-wf τ₂-wf ⁎⟧
    ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ rewrite (isPosetUnique τ₀-wf τ₁-wf) | isPosetUnique τ₁×τ₂-wf (ProductPoset τ₁-wf τ₂-wf) = 
      ⟦_⊢⟧ {τ₀-wf = ProductPoset τ₁-wf τ₂-wf} Γ₀∣R₀⊢ePair∣τ₁×τ₂

⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyProj2 {n} {Γ₀} {R₀} {ePair} {τ₁} {τ₂} Γ₀∣R₀⊢ePair∣τ₁×τ₂) = 
  ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ >> π₂ {⟦ τ₁-wf ⁎⟧} {⟦ τ₀-wf ⁎⟧}
  where
    τ₁×τ₂-wf : IsPoset (τProduct τ₁ τ₂)
    τ₁×τ₂-wf = τRes-wf Γ₀∣R₀⊢ePair∣τ₁×τ₂

    τ₁-wf : IsPoset τ₁
    τ₁-wf with τ₁×τ₂-wf
    τ₁-wf | ProductPoset goal _ = goal

    τ₂-wf : IsPoset τ₂
    τ₂-wf with τ₁×τ₂-wf
    τ₂-wf | ProductPoset _ goal = goal

    ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ : ⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ ⟦ ProductPoset τ₁-wf τ₀-wf ⁎⟧
    ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ rewrite (isPosetUnique τ₀-wf τ₂-wf) | isPosetUnique τ₁×τ₂-wf (ProductPoset τ₁-wf τ₂-wf) = 
      ⟦_⊢⟧ {τ₀-wf = ProductPoset τ₁-wf τ₂-wf} Γ₀∣R₀⊢ePair∣τ₁×τ₂



