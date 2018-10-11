module SemTyping where

open import Data.Vec
open import Data.Nat hiding (_≤_ ; _≥_)  
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Vec.Relation.Pointwise.Inductive as VPW
open import Data.List.All
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as PE
open import Function using (_$_)

open import Scalars
open import Syntax
open import Kinding
open import Typing
open import Util
open import FinPoset
open import Preorders
open import PreorderArrows
open import SemScalars
open import SemKinding
open import SemilatIso
open import Relation.Binary.Lattice
open import RelationalStructures
open import FreeForgetfulAdjunction
open import FreeSemilattice hiding (∷-Free ; []-Free ; FP-BJS ; ⊥ ; _∨_)


_R≤_ : {n : ℕ} → (Vec q n) → (Vec q n) → Set
R₁ R≤ R₂ = VPW.Pointwise _q≤_ R₁ R₂

R≤R+S : ∀ {n : ℕ} → (R S : Vec q n) → R R≤ (R R+ S)
R≤R+S {n} R S = R≤R+S' {n} R S
  where
    R≤R+S' : {n : ℕ} → (R S : Vec q n) → R R≤ (R R+ S)
    R≤R+S' (q₁ ∷ R) (q₂ ∷ S) = q₁≤q₁+q₂ ∷ (R≤R+S' R S)
    R≤R+S' {n} [] [] = []

S≤R+S : ∀ {n : ℕ} (R S : Vec q n) → S R≤ (R R+ S)
S≤R+S {n} R S = S≤R+S' {n} R S
  where
    S≤R+S' : {n : ℕ} → (R S : Vec q n) → S R≤ (R R+ S)
    S≤R+S' (q₁ ∷ R) (q₂ ∷ S) = q₂≤q₁+q₂ ∷ (S≤R+S' R S)
    S≤R+S' {n} [] [] = []

⟦_Γ∣_R⟧ : {n : ℕ} → (Γ : Vec wfτ n) → (R : Vec q n) → Preorder l0 l0 l0
⟦ []  Γ∣ [] R⟧ = unitPreorder
  where
    open import Data.Unit renaming (preorder to unitPreorder)
⟦ (τ₀ , poset-τ₀) ∷ Γ₀  Γ∣ q₀ ∷ R₀ R⟧ = ×-preorder first rest
  where
    open import Data.Product.Relation.Pointwise.NonDependent

    rest : Preorder l0 l0 l0
    rest = ⟦ Γ₀ Γ∣ R₀ R⟧

    first : Preorder l0 l0 l0
    first = ⟦ q₀ q⟧ ⟦ poset-τ₀ ⁎⟧' 

strengthenR : {n : ℕ} → (Γ₀ : Vec wfτ n) → (R₀ : Vec q n) → (R₀' : Vec q n) → (VPW.Pointwise _q≤_ R₀' R₀) → 
              (⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₀' R⟧)
strengthenR {.0} Γ₀ .[] .[] [] = record
  { fun = λ x → x
  ; monotone = λ {x} {y} x≤y → x≤y
  }
strengthenR {(suc n')} (wfτ ∷ Γ₀') (q₀ ∷ R₀) (q₀' ∷ R₀') (q₀≤q₀' ∷ R₀≤R₀') = 
  (q≤⟦ q₀≤q₀' ⟧ ⟦ proj₂ wfτ ⁎⟧') ⟨×⟩ (strengthenR Γ₀' R₀ R₀' R₀≤R₀')  

-- structural comultiplication
Δ : {n : ℕ} → (q₀ : q) → (Γ₀ : Vec wfτ n) → (R₀ : Vec q n) → ⟦ Γ₀ Γ∣ (q₀ qR∘ R₀) R⟧ ⇒ (⟦ q₀ q⟧ ⟦ Γ₀ Γ∣ R₀ R⟧)
--[[[
Δ {n} q₀ (wfτ₀ ∷ Γ₀) (r₀ ∷ R₀) =
  (δ q₀ r₀ ⟦ proj₂ wfτ₀ ⁎⟧') ⟨×⟩ (Δ q₀ Γ₀ R₀) >> p  
  where
    p : (×-preorder (⟦ q₀ q⟧ (⟦ r₀ q⟧ ⟦ proj₂ wfτ₀ ⁎⟧')) (⟦ q₀ q⟧ ⟦ Γ₀ Γ∣ R₀ R⟧)) ⇒ (⟦ q₀ q⟧ $ ×-preorder (⟦ r₀ q⟧ ⟦ proj₂ wfτ₀ ⁎⟧') ⟦ Γ₀ Γ∣ R₀ R⟧)
    p = q-cartesian⃖ (⟦ r₀ q⟧ ⟦ proj₂ wfτ₀ ⁎⟧') ⟦ Γ₀ Γ∣ R₀ R⟧ q₀ 
Δ {.0} qMono [] [] =
  record
  { fun = λ x → tt
  ; monotone = λ {x} {y} x≤y → Preorder.refl unitPreorder
  }
  where
    open import Data.Unit renaming (preorder to unitPreorder)
    open import UnitPoset
Δ {.0} qAnti [] [] =
  record
  { fun = λ x → tt
  ; monotone = λ {x} {y} x≤y → Preorder.refl unitPreorder
  }
  where
    open import Data.Unit renaming (preorder to unitPreorder)
    open import UnitPoset
Δ {.0} qConst [] [] =
  record
  { fun = λ x → tt
  ; monotone = λ {x} {y} x≤y → ε
  }
  where
    open import Data.Unit
    open import Relation.Binary.Closure.ReflexiveTransitive
Δ {.0} qAny [] [] =
  record
  { fun = λ x → tt
  ; monotone = λ {x} {y} x≤y → (PE.refl , PE.refl)
  }
  where
    open import Relation.Binary.PropositionalEquality as PE
    open import Data.Unit renaming (preorder to unitPreorder)
--]]]

{-
Δ⁻¹ : {n : ℕ} → (q₀ : q) → (Γ₀ : Vec wfτ n) → (R₀ : Vec q n) → (⟦ q₀ q⟧ ⟦ Γ₀ Γ∣ R₀ R⟧) ⇒ ⟦ Γ₀ Γ∣ (q₀ qR∘ R₀) R⟧
--[[[
Δ⁻¹ {n} q₀ (wfτ₀ ∷ Γ₀) (r₀ ∷ R₀) =
  p >> (δ⁻¹ q₀ r₀ ⟦ proj₂ wfτ₀ ⁎⟧) ⟨×⟩ (Δ⁻¹ q₀ Γ₀ R₀)  
  where
    p : (⟦ q₀ q⟧ $ ×-poset (⟦ r₀ q⟧ ⟦ proj₂ wfτ₀ ⁎⟧) ⟦ Γ₀ Γ∣ R₀ R⟧) ⇒ (×-poset (⟦ q₀ q⟧ (⟦ r₀ q⟧ ⟦ proj₂ wfτ₀ ⁎⟧)) (⟦ q₀ q⟧ ⟦ Γ₀ Γ∣ R₀ R⟧))
    p = q-cartesian⃗ (⟦ r₀ q⟧ ⟦ proj₂ wfτ₀ ⁎⟧) ⟦ Γ₀ Γ∣ R₀ R⟧ q₀ 
Δ⁻¹ {n} q₀ [] [] =
  record
  { fun = λ x → tt
  ; monotone = λ {x} {y} x≤y → Poset.refl ⊤≤-poset
  }
  where
    open import Data.Unit
    open import UnitPoset
--]]]
-}

⟦_⊢⟧ : {n : ℕ} → {Γ₀ : Vec wfτ n} → {R₀ : Vec q n} → {e₀ : e} → {τ₀ : τ} → {τ₀-wf : IsPoset τ₀} →
       (x : Γ₀ ∣ R₀ ⊢ e₀ ∣ τ₀) → ⟦ Γ₀ Γ∣ R₀ R⟧  ⇒ ⟦ τ₀-wf ⁎⟧' 
{-
--[[[
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyBot {n} {Γ} {τ₀} {τ₀'} {τ₀-semilat}) = 
--[[[
  record
  { fun = λ _ → ⊥'
  ; monotone = λ {_} {_} _ → codP.refl
  }
  where
    open import SemSemilatKinding
    open import Relation.Binary.Lattice
    open SemSemilatCore ⟦ τ₀-semilat ⁂⟧
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
    open import SemSemilatKinding
    open import Relation.Binary.Lattice
    open import Data.Product.Relation.Pointwise.NonDependent
    open SemSemilatCore ⟦ τ₀-semilat ⁂⟧
    open BoundedJoinSemilattice S
    module codP = IsPartialOrder (Poset.isPartialOrder ⟦ τ₀-wf ⁎⟧)

    R₁≤R₁+R₂ : R₁ R≤ (R₁ R+ R₂)
    R₁≤R₁+R₂ = R≤R+S R₁ R₂
    
    R₂≤R₁+R₂ : R₂ R≤ (R₁ R+ R₂)  
    R₂≤R₁+R₂ = S≤R+S R₁ R₂

    wk1 : ⟦ Γ₀ Γ∣ R₁ R+ R₂ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₁ R⟧
    wk1 = strengthenR Γ₀ (R₁ R+ R₂) R₁ R₁≤R₁+R₂

    wk2 : ⟦ Γ₀ Γ∣ R₁ R+ R₂ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₂ R⟧
    wk2 = strengthenR Γ₀ (R₁ R+ R₂) R₂ R₂≤R₁+R₂

    f₁ : ⟦ Γ₀ Γ∣ R₁ R⟧ ⇒ ⟦ τ₀-wf ⁎⟧' 
    f₁ = ⟦_⊢⟧ {n} {Γ₀} {R₁} {e₁} {τ₀} {τ₀-wf} Γ∣R₁⊢e₁∣τ₀
    
    f₂ : ⟦ Γ₀ Γ∣ R₂ R⟧ ⇒ ⟦ τ₀-wf ⁎⟧'
    f₂ = ⟦_⊢⟧ {n} {Γ₀} {R₂} {e₂} {τ₀} {τ₀-wf} Γ∣R₂⊢e₂∣τ₀

    _∨'_ : (×-preorder ⟦ τ₀-wf ⁎⟧' ⟦ τ₀-wf ⁎⟧') ⇒ ⟦ τ₀-wf ⁎⟧'
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
--[[[ 
  with τRes-wf σ₁∷Γ∣q₁∷R⊢body∣τ₁ 
⟦_⊢⟧ {τ₀-wf = FunPoset domPoset codPoset} (TyAbs {n} {Γ₀} {R₀} {q₁} {body} {σ₁} {τ₁} {σ₁-wf} (σ₁∷Γ∣q₁∷R⊢body∣τ₁)) | τ₁-wf 
  rewrite isPosetUnique codPoset τ₁-wf | isPosetUnique domPoset σ₁-wf =
  Λ ⟦σ₁∷Γ∣q₁∷R⟧⇒⟦τ₁⟧ 
  where
    ⟦σ₁∷Γ∣q₁∷R⟧⇒⟦τ₁⟧ : ⟦ (σ₁ , σ₁-wf) ∷ Γ₀ Γ∣ q₁ ∷ R₀ R⟧ ⇒ ⟦ τ₁-wf ⁎⟧'
    ⟦σ₁∷Γ∣q₁∷R⟧⇒⟦τ₁⟧ = ⟦_⊢⟧ {τ₀-wf = τ₁-wf} σ₁∷Γ∣q₁∷R⊢body∣τ₁
--]]]
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyApp {n} {Γ₀} {R₁} {R₂} {q₀} {e₁} {e₂} {σ₀} {τ₀} Γ₀∣R₁⊢e₁∣σ₀→τ₀ Γ₀∣R₂⊢e₂∣σ₀) =
--[[[
  ⟨ ⟦Γ₀∣R₁+q₀R₂⟧⇒⟦Γ₀∣q₀R₂⟧ >> (Δ q₀ Γ₀ R₂) >> ⟦q₀⟧⟦Γ₀∣R₂⟧⇒⟦q₀⟧⟦σ₀⟧ , ⟦Γ₀∣R₁+q₀R₂⟧⇒⟦Γ₀∣R₁⟧ >> ⟦Γ₀∣R₁⟧⇒⟦q₀σ₀⇒τ₀⟧ ⟩ >> ev
  where
    σ₀→τ₀-wf : IsPoset (τFun σ₀ q₀ τ₀)
    σ₀→τ₀-wf = τRes-wf Γ₀∣R₁⊢e₁∣σ₀→τ₀

    σ₀-wf : IsPoset σ₀
    σ₀-wf = τRes-wf Γ₀∣R₂⊢e₂∣σ₀

    σ₀→τ₀-wf' : IsPoset (τFun σ₀ q₀ τ₀)
    σ₀→τ₀-wf' = FunPoset σ₀-wf τ₀-wf

    R₁≤R₁+q₀R₂ : R₁ R≤ (R₁ R+ (q₀ qR∘ R₂))
    R₁≤R₁+q₀R₂ = R≤R+S R₁ (q₀ qR∘ R₂)

    q₀R₂≤R₁+q₀R₂ : (q₀ qR∘ R₂) R≤ (R₁ R+ (q₀ qR∘ R₂))
    q₀R₂≤R₁+q₀R₂ = S≤R+S R₁ (q₀ qR∘ R₂)
 
    ⟦Γ₀∣R₁+q₀R₂⟧⇒⟦Γ₀∣R₁⟧ : ⟦ Γ₀ Γ∣ (R₁ R+ (q₀ qR∘ R₂)) R⟧ ⇒ ⟦ Γ₀ Γ∣ R₁ R⟧
    ⟦Γ₀∣R₁+q₀R₂⟧⇒⟦Γ₀∣R₁⟧ = strengthenR Γ₀ (R₁ R+ (q₀ qR∘ R₂)) R₁ R₁≤R₁+q₀R₂

    ⟦Γ₀∣R₁+q₀R₂⟧⇒⟦Γ₀∣q₀R₂⟧ : ⟦ Γ₀ Γ∣ (R₁ R+ (q₀ qR∘ R₂)) R⟧ ⇒ ⟦ Γ₀ Γ∣ (q₀ qR∘ R₂) R⟧
    ⟦Γ₀∣R₁+q₀R₂⟧⇒⟦Γ₀∣q₀R₂⟧ = strengthenR Γ₀ (R₁ R+ (q₀ qR∘ R₂)) (q₀ qR∘ R₂) q₀R₂≤R₁+q₀R₂

    ⟦Γ₀∣R₁⟧⇒⟦q₀σ₀⇒τ₀⟧ : ⟦ Γ₀ Γ∣ R₁ R⟧ ⇒ ⟦ σ₀→τ₀-wf' ⁎⟧'
    ⟦Γ₀∣R₁⟧⇒⟦q₀σ₀⇒τ₀⟧ rewrite isPosetUnique σ₀→τ₀-wf' σ₀→τ₀-wf = ⟦_⊢⟧ {τ₀-wf = σ₀→τ₀-wf'} Γ₀∣R₁⊢e₁∣σ₀→τ₀

    ⟦Γ₀∣R₁+q₀R₂⟧⇒⟦q₀σ₀⇒τ₀⟧ : ⟦ Γ₀ Γ∣ (R₁ R+ (q₀ qR∘ R₂)) R⟧ ⇒ ⟦ σ₀→τ₀-wf' ⁎⟧'
    ⟦Γ₀∣R₁+q₀R₂⟧⇒⟦q₀σ₀⇒τ₀⟧ rewrite isPosetUnique σ₀→τ₀-wf' σ₀→τ₀-wf' = ⟦Γ₀∣R₁+q₀R₂⟧⇒⟦Γ₀∣R₁⟧ >> ⟦Γ₀∣R₁⟧⇒⟦q₀σ₀⇒τ₀⟧

    ⟦Γ₀∣R₂⟧⇒⟦σ₀⟧ : ⟦ Γ₀ Γ∣ R₂ R⟧ ⇒ ⟦ σ₀-wf ⁎⟧' 
    ⟦Γ₀∣R₂⟧⇒⟦σ₀⟧ = ⟦_⊢⟧ {τ₀-wf = σ₀-wf} Γ₀∣R₂⊢e₂∣σ₀

    ⟦q₀⟧⟦Γ₀∣R₂⟧⇒⟦q₀⟧⟦σ₀⟧ : (⟦ q₀ q⟧ ⟦ Γ₀ Γ∣ R₂ R⟧) ⇒ (⟦ q₀ q⟧ ⟦ σ₀-wf ⁎⟧')
    ⟦q₀⟧⟦Γ₀∣R₂⟧⇒⟦q₀⟧⟦σ₀⟧ = ⟦ q₀ q⇒⟧ ⟦Γ₀∣R₂⟧⇒⟦σ₀⟧
--]]]
⟦_⊢⟧ {τ₀-wf = ProductPoset posetL posetR} (TyPair {n} {Γ₀} {R₁} {R₂} {e₁} {e₂} {τ₁} {τ₂} Γ₀∣R₁⊢e₁∣τ₁ Γ₀∣R₂⊢e₂∣τ₂)
--[[[
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
    R₁≤R₁+R₂ = R≤R+S R₁ R₂
    
    R₂≤R₁+R₂ : R₂ R≤ (R₁ R+ R₂)  
    R₂≤R₁+R₂ = S≤R+S R₁ R₂

    wk1 : ⟦ Γ₀ Γ∣ R₁ R+ R₂ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₁ R⟧
    wk1 = strengthenR Γ₀ (R₁ R+ R₂) R₁ R₁≤R₁+R₂

    wk2 : ⟦ Γ₀ Γ∣ R₁ R+ R₂ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₂ R⟧
    wk2 = strengthenR Γ₀ (R₁ R+ R₂) R₂ R₂≤R₁+R₂    
 
    ⟦Γ₀∣R₁⊢e₁∣τ₁⟧ : ⟦ Γ₀ Γ∣ R₁ R⟧ ⇒ ⟦ τ₁-wf ⁎⟧' 
    ⟦Γ₀∣R₁⊢e₁∣τ₁⟧ = ⟦_⊢⟧ {τ₀-wf = τ₁-wf} Γ₀∣R₁⊢e₁∣τ₁   

    ⟦Γ₀∣R₂⊢e₂∣τ₂⟧ : ⟦ Γ₀ Γ∣ R₂ R⟧ ⇒ ⟦ τ₂-wf ⁎⟧'
    ⟦Γ₀∣R₂⊢e₂∣τ₂⟧ = ⟦_⊢⟧ {τ₀-wf = τ₂-wf} Γ₀∣R₂⊢e₂∣τ₂   
--]]]
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyProj1 {n} {Γ₀} {R₀} {ePair} {τ₁} {τ₂} Γ₀∣R₀⊢ePair∣τ₁×τ₂) = 
--[[[
  ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ >> π₁ {⟦ τ₀-wf ⁎⟧'} {⟦ τ₂-wf ⁎⟧'}
  where
    τ₁×τ₂-wf : IsPoset (τProduct τ₁ τ₂)
    τ₁×τ₂-wf = τRes-wf Γ₀∣R₀⊢ePair∣τ₁×τ₂

    τ₁-wf : IsPoset τ₁
    τ₁-wf with τ₁×τ₂-wf
    τ₁-wf | ProductPoset goal _ = goal

    τ₂-wf : IsPoset τ₂
    τ₂-wf with τ₁×τ₂-wf
    τ₂-wf | ProductPoset _ goal = goal

    ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ : ⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ ⟦ ProductPoset τ₀-wf τ₂-wf ⁎⟧'
    ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ rewrite (isPosetUnique τ₀-wf τ₁-wf) | isPosetUnique τ₁×τ₂-wf (ProductPoset τ₁-wf τ₂-wf) = 
      ⟦_⊢⟧ {τ₀-wf = ProductPoset τ₁-wf τ₂-wf} Γ₀∣R₀⊢ePair∣τ₁×τ₂
--]]]
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyProj2 {n} {Γ₀} {R₀} {ePair} {τ₁} {τ₂} Γ₀∣R₀⊢ePair∣τ₁×τ₂) = 
--[[[
  ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ >> π₂ {⟦ τ₁-wf ⁎⟧'} {⟦ τ₀-wf ⁎⟧'}
  where
    τ₁×τ₂-wf : IsPoset (τProduct τ₁ τ₂)
    τ₁×τ₂-wf = τRes-wf Γ₀∣R₀⊢ePair∣τ₁×τ₂

    τ₁-wf : IsPoset τ₁
    τ₁-wf with τ₁×τ₂-wf
    τ₁-wf | ProductPoset goal _ = goal

    τ₂-wf : IsPoset τ₂
    τ₂-wf with τ₁×τ₂-wf
    τ₂-wf | ProductPoset _ goal = goal

    ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ : ⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ ⟦ ProductPoset τ₁-wf τ₀-wf ⁎⟧'
    ⟦Γ₀∣R⊢ePair∣τ₁×τ₂⟧ rewrite (isPosetUnique τ₀-wf τ₂-wf) | isPosetUnique τ₁×τ₂-wf (ProductPoset τ₁-wf τ₂-wf) = 
      ⟦_⊢⟧ {τ₀-wf = ProductPoset τ₁-wf τ₂-wf} Γ₀∣R₀⊢ePair∣τ₁×τ₂
--]]]
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyCase {n} {Γ₀} {R₀} {R₁} {R₂} {e₀} {e₁} {e₂} {τ₁} {τ₂} {τ₀} {τ₁-wf} {τ₂-wf} {q₁} {q₂} 
                             Γ₀∣R₀⊢e₀∣τ₁+τ₂ τ₁∷Γ∣q₁∷R₁⊢e₁:τ₀ τ₂∷Γ∣q₂∷R₂⊢e₂:τ₀) =
--[[[
  ⟨ ⟦Γ₀∣···⟧⇒⟦q₁τ₁+q₂τ₂⟧ , ⟦Γ₀∣···⟧⇒⟦q₁τ₁+q₂τ₂⇒τ₀⟧ ⟩ >> ev  
  where
    open import Data.Sum.Relation.Pointwise

    τ₁+τ₂-wf : IsPoset (τSum τ₁ τ₂)
    τ₁+τ₂-wf = τRes-wf Γ₀∣R₀⊢e₀∣τ₁+τ₂

    τ₁+τ₂-wf' : IsPoset (τSum τ₁ τ₂)
    τ₁+τ₂-wf' = SumPoset τ₁-wf τ₂-wf

    R₁≤R₁+R₂ : R₁ R≤ (R₁ R+ R₂)
    R₁≤R₁+R₂ = R≤R+S R₁ R₂
    
    R₂≤R₁+R₂ : R₂ R≤ (R₁ R+ R₂)  
    R₂≤R₁+R₂ = S≤R+S R₁ R₂
    
    --todo: add fixity annotations to R+ and qR∘ to make this more readable
    R₁+R₂≤··· : (R₁ R+ R₂) R≤ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂))
    R₁+R₂≤··· = S≤R+S ((q₁ q+ q₂) qR∘ R₀) (R₁ R+ R₂)

    ⟨q₁+q₂⟩∘R₀≤··· : ((q₁ q+ q₂) qR∘ R₀) R≤ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂))
    ⟨q₁+q₂⟩∘R₀≤··· = R≤R+S ((q₁ q+ q₂) qR∘ R₀) (R₁ R+ R₂)

    R₁≤··· : R₁ R≤ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂))
    R₁≤··· = VPW.trans (Preorder.trans QP.≤-preorder) R₁≤R₁+R₂ R₁+R₂≤···
    
    R₂≤··· : R₂ R≤ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂))
    R₂≤··· = VPW.trans (Preorder.trans QP.≤-preorder) R₂≤R₁+R₂ R₁+R₂≤···
    
    ⟦Γ₀∣R₁⟧⇒⟦q₁τ₁⇒τ₀⟧ : ⟦ Γ₀ Γ∣ R₁ R⟧ ⇒ (⇒-preorder (⟦ q₁ q⟧ ⟦ τ₁-wf ⁎⟧') ⟦ τ₀-wf ⁎⟧')
    ⟦Γ₀∣R₁⟧⇒⟦q₁τ₁⇒τ₀⟧ = Λ (⟦_⊢⟧ {τ₀-wf = τ₀-wf} τ₁∷Γ∣q₁∷R₁⊢e₁:τ₀)
    
    ⟦Γ₀∣R₂⟧⇒⟦q₂τ₂⇒τ₀⟧ : ⟦ Γ₀ Γ∣ R₂ R⟧ ⇒ (⇒-preorder (⟦ q₂ q⟧ ⟦ τ₂-wf ⁎⟧') ⟦ τ₀-wf ⁎⟧')
    ⟦Γ₀∣R₂⟧⇒⟦q₂τ₂⇒τ₀⟧ = Λ (⟦_⊢⟧ {τ₀-wf = τ₀-wf} τ₂∷Γ∣q₂∷R₂⊢e₂:τ₀)

    ⟦Γ₀∣···⟧⇒⟦Γ₀∣R₁⟧ :  ⟦ Γ₀ Γ∣ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂)) R⟧ ⇒ ⟦ Γ₀ Γ∣ R₁ R⟧
    ⟦Γ₀∣···⟧⇒⟦Γ₀∣R₁⟧ = strengthenR Γ₀ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂)) R₁ R₁≤···
    
    ⟦Γ₀∣···⟧⇒⟦Γ₀∣R₂⟧ :  ⟦ Γ₀ Γ∣ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂)) R⟧ ⇒ ⟦ Γ₀ Γ∣ R₂ R⟧
    ⟦Γ₀∣···⟧⇒⟦Γ₀∣R₂⟧ = strengthenR Γ₀ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂)) R₂ R₂≤···

    ⟦Γ₀∣···⟧⇒⟦Γ₀∣⟨q₁+q₂⟩∘R₀⟧ : ⟦ Γ₀ Γ∣ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂)) R⟧ ⇒ ⟦ Γ₀ Γ∣ (q₁ q+ q₂) qR∘ R₀ R⟧  
    ⟦Γ₀∣···⟧⇒⟦Γ₀∣⟨q₁+q₂⟩∘R₀⟧ = strengthenR Γ₀ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂)) ((q₁ q+ q₂) qR∘ R₀) ⟨q₁+q₂⟩∘R₀≤··· 

    ⟦q₁+q₂⟧⟦Γ₀∣R₀⟧⇒⟦q₁+q₂⟧⟦τ₁+τ₂⟧ : (⟦ q₁ q+ q₂ q⟧ ⟦ Γ₀ Γ∣ R₀ R⟧) ⇒ (⟦ q₁ q+ q₂ q⟧ ⟦ τ₁+τ₂-wf' ⁎⟧')
    ⟦q₁+q₂⟧⟦Γ₀∣R₀⟧⇒⟦q₁+q₂⟧⟦τ₁+τ₂⟧ = 
      ⟦ q₁ q+ q₂ q⇒⟧ (⟦_⊢⟧ {τ₀-wf = τ₁+τ₂-wf'} Γ₀∣R₀⊢e₀∣τ₁+τ₂)  

    ⟦Γ₀∣⟨q₁+q₂⟩∘R₀⟧⇒⟦q₁+q₂⟧⟦τ₁⟧+⟦q₁+q₂⟧⟦τ₂⟧ : 
      ⟦ Γ₀ Γ∣ (q₁ q+ q₂) qR∘ R₀ R⟧ ⇒ 
      (⊎-preorder0 (⟦ (q₁ q+ q₂) q⟧ ⟦ τ₁-wf ⁎⟧') (⟦ (q₁ q+ q₂) q⟧ ⟦ τ₂-wf ⁎⟧'))  
    ⟦Γ₀∣⟨q₁+q₂⟩∘R₀⟧⇒⟦q₁+q₂⟧⟦τ₁⟧+⟦q₁+q₂⟧⟦τ₂⟧ =  
      (Δ (q₁ q+ q₂) Γ₀ R₀) >> ⟦q₁+q₂⟧⟦Γ₀∣R₀⟧⇒⟦q₁+q₂⟧⟦τ₁+τ₂⟧ >> (q-preserves-+⃗ ⟦ τ₁-wf ⁎⟧' ⟦ τ₂-wf ⁎⟧' (q₁ q+ q₂))  

    ⟦Γ₀∣···⟧⇒⟦q₁τ₁+q₂τ₂⟧ : ⟦ Γ₀ Γ∣ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂)) R⟧ ⇒ 
      (⊎-preorder0 (⟦ q₁ q⟧ ⟦ τ₁-wf ⁎⟧') (⟦ q₂ q⟧ ⟦ τ₂-wf ⁎⟧'))   
    ⟦Γ₀∣···⟧⇒⟦q₁τ₁+q₂τ₂⟧ = 
      ⟦Γ₀∣···⟧⇒⟦Γ₀∣⟨q₁+q₂⟩∘R₀⟧ >> 
      ⟦Γ₀∣⟨q₁+q₂⟩∘R₀⟧⇒⟦q₁+q₂⟧⟦τ₁⟧+⟦q₁+q₂⟧⟦τ₂⟧ >> 
      (q≤⟦ q₁≤q₁+q₂ {q₁} {q₂} ⟧ ⟦ τ₁-wf ⁎⟧' ⟨+⟩ q≤⟦ q₂≤q₁+q₂ {q₁} {q₂} ⟧ ⟦ τ₂-wf ⁎⟧') 

    ⟦Γ₀∣···⟧⇒⟦q₁τ₁+q₂τ₂⇒τ₀⟧ : 
      ⟦ Γ₀ Γ∣ (((q₁ q+ q₂) qR∘ R₀) R+ (R₁ R+ R₂)) R⟧ ⇒ 
      (⇒-preorder (⊎-preorder (⟦ q₁ q⟧ ⟦ τ₁-wf ⁎⟧') (⟦ q₂ q⟧ ⟦ τ₂-wf ⁎⟧')) ⟦ τ₀-wf ⁎⟧')
    ⟦Γ₀∣···⟧⇒⟦q₁τ₁+q₂τ₂⇒τ₀⟧ = 
      ⟨ ⟦Γ₀∣···⟧⇒⟦Γ₀∣R₁⟧ >> ⟦Γ₀∣R₁⟧⇒⟦q₁τ₁⇒τ₀⟧ , ⟦Γ₀∣···⟧⇒⟦Γ₀∣R₂⟧ >> ⟦Γ₀∣R₂⟧⇒⟦q₂τ₂⇒τ₀⟧ ⟩ >> [[+]]
--]]]

⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyInl {n} {Γ₀} {R₀} {e} {τL} {τR} {τR-wf} Γ₀∣R₀⊢e∣τL) 
  with τL-wf | isPosetUnique τ₀-wf (SumPoset τL-wf τR-wf)
  where
    τL-wf : IsPoset τL
    τL-wf = τRes-wf Γ₀∣R₀⊢e∣τL
⟦_⊢⟧ {τ₀-wf = _} (TyInl {n} {Γ₀} {R₀} {e} {τL} {τR} {τR-wf} Γ₀∣R₀⊢e∣τL) | τL-wf | PE.refl =
  ⟦Γ₀∣R₀⟧⇒⟦τL⟧ >> κ₁ 
  where
    ⟦Γ₀∣R₀⟧⇒⟦τL⟧ : ⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ ⟦ τL-wf ⁎⟧' 
    ⟦Γ₀∣R₀⟧⇒⟦τL⟧ = ⟦_⊢⟧ {τ₀-wf = τL-wf} Γ₀∣R₀⊢e∣τL 
    
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyInr {n} {Γ₀} {R₀} {e} {τL} {τR} {τL-wf} Γ₀∣R₀⊢e∣τR) 
  with τR-wf | isPosetUnique τ₀-wf (SumPoset τL-wf τR-wf)
  where
    τR-wf : IsPoset τR
    τR-wf = τRes-wf Γ₀∣R₀⊢e∣τR
⟦_⊢⟧ {τ₀-wf = _} (TyInr {n} {Γ₀} {R₀} {e} {τL} {τR} {τL-wf} Γ₀∣R₀⊢e∣τR) | τR-wf | PE.refl =
  ⟦Γ₀∣R₀⟧⇒⟦τR⟧ >> κ₂ 
  where
    ⟦Γ₀∣R₀⟧⇒⟦τR⟧ : ⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ ⟦ τR-wf ⁎⟧' 
    ⟦Γ₀∣R₀⟧⇒⟦τR⟧ = ⟦_⊢⟧ {τ₀-wf = τR-wf} Γ₀∣R₀⊢e∣τR 

⟦_⊢⟧ {τ₀-wf = FunPoset τ₁-wf τ₂-wf} 
     (TyHom {n} {Γ₀} {R₀} {e₀} {τ₁} {τ₁'} {τ₂} {τ₂'} {τ₁⁂} {τ₂⁂} {τ₁'-wf} τ₁'∷Γ∣+∷R₀⊢e₀∣τ₂) =
  ⟦Γ∣R₀⟧⇒⟦P⇒S⟧ >> (♯ P₁ S₂) >> precomp-f 
  where
    open import Relation.Binary.Lattice
    open import SemSemilatKinding
    open import RelationalStructures
    open import FreeForgetfulAdjunction

    semilat₁ : SemSemilatCore _ _ _ _ _ _ _ τ₁⁂
    semilat₁ = ⟦ τ₁⁂ ⁂⟧

    semilatIso₁ : SemSemilatIso _ _ _ _ _ _ _ τ₁⁂
    semilatIso₁ = ⟦ τ₁⁂ ⁂iso⟧

    semilat₂ : SemSemilatCore _ _ _ _ _ _ _ τ₂⁂
    semilat₂ = ⟦ τ₂⁂ ⁂⟧ 

    open SemSemilatCore semilat₂ renaming (S to S₂ ; US to US₂)
    open SemSemilatCore semilat₁ renaming (P to P₁ ; i to i₁ ; US to US₁ ; S to S₁) 
    open SemSemilatIso semilatIso₁ renaming (f to f₁ ; g to g₁)
    open import FreeSemilattice P₁ renaming (preorder to FP₁' ; FP-BJS to FP₁-BJS) 
    open BoundedJoinSemilattice S₂ renaming (preorder to S₂')

    τ₁-wf' : IsPoset τ₁
    τ₁-wf' = semilat→poset τ₁⁂

    τ₁'-wf' : IsPoset τ₁'
    τ₁'-wf' = delta→poset (semilat→delta τ₁⁂)

    τ₂-wf' : IsPoset τ₂
    τ₂-wf' = semilat→poset τ₂⁂

    τ₂-wf≡τ₂-wf' : τ₂-wf ≡ τ₂-wf' 
    τ₂-wf≡τ₂-wf' = isPosetUnique τ₂-wf τ₂-wf'

    τ₁-wf≡τ₁-wf' : τ₁-wf ≡ τ₁-wf'
    τ₁-wf≡τ₁-wf' = isPosetUnique τ₁-wf τ₁-wf'

    τ₁'-wf≡t₁'-wf' : τ₁'-wf ≡ τ₁'-wf'
    τ₁'-wf≡t₁'-wf' = isPosetUnique τ₁'-wf τ₁'-wf'
    
    ⟦Γ∣R₀⟧⇒⟦τ₁'⇒τ₂⟧ : ⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ (⇒-preorder ⟦ τ₁'-wf' ⁎⟧' ⟦ τ₂-wf ⁎⟧') 
    ⟦Γ∣R₀⟧⇒⟦τ₁'⇒τ₂⟧ rewrite τ₁'-wf≡t₁'-wf' = Λ (⟦_⊢⟧ {τ₀-wf = τ₂-wf} τ₁'∷Γ∣+∷R₀⊢e₀∣τ₂)

    precomp-f : (⇒-preorder FP₁' S₂') ⇒ (⇒-preorder ⟦ τ₁-wf ⁎⟧' ⟦ τ₂-wf ⁎⟧')   
    precomp-f rewrite τ₁-wf≡τ₁-wf' | τ₂-wf≡τ₂-wf' | US₂ | (PE.sym US₁) = precomp ((⇉-to-⇒ {S = S₁} {T = FP₁-BJS} f₁))

    ⟦Γ∣R₀⟧⇒⟦P⇒S⟧ : ⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ (⇒-preorder (DeltaPoset.preorder P₁) (BoundedJoinSemilattice.preorder S₂))
    ⟦Γ∣R₀⟧⇒⟦P⇒S⟧ rewrite US₂ | PE.sym τ₂-wf≡τ₂-wf' = ⟦Γ∣R₀⟧⇒⟦τ₁'⇒τ₂⟧ >> precomp (↣+-to-⇒ i₁)

⟦_⊢⟧ {τ₀-wf = DictPoset isStosetDom isSemilatCod} (TySng {n} {Γ₀} {R₁} {R₂} {R₃} {eKey} {τKey} {eVal} {τVal} {τValDelta} isStosetKey isSemilatVal x₂ x₃ x₄) with (isSemilatDeltaUnique isSemilatCod isSemilatVal)
⟦_⊢⟧ {τ₀-wf = DictPoset isStosetDom isSemilatCod} (TySng {n} {Γ₀} {R₁} {R₂} {R₃} {eKey} {τKey} {eVal} {τVal} {τValDelta} isStosetKey isSemilatVal x₂ x₃ x₄) | PE.refl with isStosetUnique isStosetDom isStosetKey | isSemilatUnique isSemilatCod isSemilatVal  
⟦_⊢⟧ {τ₀-wf = DictPoset isStosetCod isSemilatCod} (TySng {n} {Γ₀} {R₁} {R₂} {R₃} {eKey} {τKey} {eVal} {τVal} {τValDelta} isStosetKey isSemilatVal eq Γ∣R₁⊢eKey∣τKey Γ∣R₂⊢eVal∣τVal) | PE.refl | PE.refl | PE.refl =
  ⟦Γ₀∣?R₁+R₂⟧⇒⟦?⟧⟦Γ₀∣R₁⟧×⟦Γ₀∣R₂⟧ >> (⟦?⟧⟦Γ₀∣R₁⟧⇒⟦?⟧⟦τKey⟧ ⟨×⟩ ⟦Γ₀∣R₂⟧⇒⟦τVal⟧) >> ▹-sng' 
  where
    τKey-wf : IsPoset τKey
    τKey-wf = stoset→poset isStosetKey

    τVal-wf : IsPoset τVal
    τVal-wf = semilat→poset isSemilatVal

    ?R₁≤?R₁+R₂ : (qAny qR∘ R₁) R≤ ((qAny qR∘ R₁) R+ R₂)
    ?R₁≤?R₁+R₂ = R≤R+S (qAny qR∘ R₁) R₂

    R₂≤?R₁+R₂ : R₂ R≤ ((qAny qR∘ R₁) R+ R₂)
    R₂≤?R₁+R₂ = S≤R+S (qAny qR∘ R₁) R₂

    ⟦Γ₀∣?R₁+R₂⟧⇒⟦Γ₀∣?R₁⟧ : ⟦ Γ₀ Γ∣ (qAny qR∘ R₁) R+ R₂ R⟧ ⇒ ⟦ Γ₀ Γ∣ (qAny qR∘ R₁) R⟧   
    ⟦Γ₀∣?R₁+R₂⟧⇒⟦Γ₀∣?R₁⟧ = strengthenR Γ₀ ((qAny qR∘ R₁) R+ R₂) (qAny qR∘ R₁) ?R₁≤?R₁+R₂

    ⟦Γ₀∣?R₁+R₂⟧⇒⟦Γ₀∣R₂⟧ : ⟦ Γ₀ Γ∣ (qAny qR∘ R₁) R+ R₂ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₂ R⟧   
    ⟦Γ₀∣?R₁+R₂⟧⇒⟦Γ₀∣R₂⟧ = strengthenR Γ₀ ((qAny qR∘ R₁) R+ R₂) R₂ R₂≤?R₁+R₂

    ⟦Γ₀∣?R₁+R₂⟧⇒⟦?⟧⟦Γ₀∣R₁⟧×⟦Γ₀∣R₂⟧ : ⟦ Γ₀ Γ∣ R₃ R⟧ ⇒ (×-preorder (⟦ qAny q⟧ ⟦ Γ₀ Γ∣ R₁ R⟧) ⟦ Γ₀ Γ∣ R₂ R⟧)
    ⟦Γ₀∣?R₁+R₂⟧⇒⟦?⟧⟦Γ₀∣R₁⟧×⟦Γ₀∣R₂⟧ rewrite eq = ⟨ ⟦Γ₀∣?R₁+R₂⟧⇒⟦Γ₀∣?R₁⟧ >> (Δ qAny Γ₀ R₁) , ⟦Γ₀∣?R₁+R₂⟧⇒⟦Γ₀∣R₂⟧ ⟩ 

    ⟦Γ₀∣R₁⟧⇒⟦τKey⟧ : ⟦ Γ₀ Γ∣ R₁ R⟧ ⇒ ⟦ τKey-wf ⁎⟧'
    ⟦Γ₀∣R₁⟧⇒⟦τKey⟧ = ⟦_⊢⟧ { τ₀-wf = τKey-wf } Γ∣R₁⊢eKey∣τKey 

    ⟦?⟧⟦Γ₀∣R₁⟧⇒⟦?⟧⟦τKey⟧ : (⟦ qAny q⟧ ⟦ Γ₀ Γ∣ R₁ R⟧) ⇒ (⟦ qAny q⟧ ⟦ τKey-wf ⁎⟧')
    ⟦?⟧⟦Γ₀∣R₁⟧⇒⟦?⟧⟦τKey⟧ = ⟦ qAny q⇒⟧ ⟦Γ₀∣R₁⟧⇒⟦τKey⟧      

    ⟦Γ₀∣R₂⟧⇒⟦τVal⟧ : ⟦ Γ₀ Γ∣ R₂ R⟧ ⇒ ⟦ τVal-wf ⁎⟧'
    ⟦Γ₀∣R₂⟧⇒⟦τVal⟧ = ⟦_⊢⟧ { τ₀-wf = τVal-wf}  Γ∣R₂⊢eVal∣τVal 

    ▹-sng' : (×-preorder (⟦ qAny q⟧ ⟦ τKey-wf ⁎⟧')  ⟦ τVal-wf ⁎⟧') ⇒ 
            (▹-preorder (SemStoset.T ⟦ isStosetKey ⁑⟧) (SemSemilatCore.S ⟦ isSemilatVal ⁂⟧))
    ▹-sng' rewrite PE.sym $ SemSemilatCore.US ⟦ isSemilatVal ⁂⟧ = 
      ▹-sng ⟦ τKey-wf ⁎⟧ (SemStoset.T ⟦ isStosetKey ⁑⟧) (PE.sym $ SemStoset.eq ⟦ isStosetKey ⁑⟧)
             (SemSemilatCore.S ⟦ isSemilatVal ⁂⟧) (SemSemilatCore.P ⟦ isSemilatVal ⁂⟧)
             (SemSemilatIso.f ⟦ isSemilatVal ⁂iso⟧)
-}
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyExtract {n} {q₁} {q₂} {q₃} {Γ₀} {R₁} {R₂} {R₃} {eDict} {eBody} {τKey} {τVal} {τValDelta} {τTarget} {τTargetDelta} isStosetKey isSemilatVal isSemilatTarget eq q₂≤+ q₃≤+ Γ₀∣R₁⊢eDict∣τ▹σ τ∷σ∷κ∷Γ₀∣q₁∷q₂∷q₃∷R₂⊢eBody∣κ)
--[[[
  with isPosetUnique τ₀-wf (semilat→poset isSemilatTarget)
⟦_⊢⟧ {τ₀-wf = τ₀-wf} (TyExtract {n} {q₁} {q₂} {q₃} {Γ₀} {R₁} {R₂} {R₃} {eDict} {eBody} {τKey} {τVal} {τValDelta} {τTarget} {τTargetDelta} isStosetKey isSemilatVal isSemilatTarget eq q₂≤+ q₃≤+ Γ₀∣R₁⊢eDict∣τ▹σ τ∷σ∷κ∷Γ₀∣q₁∷q₂∷q₃∷R₂⊢eBody∣κ)
  | PE.refl =
  ⟨ ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₁⟧ >> ⟦Γ₀∣R₁⟧⇒⟦τ▹σ⟧ , ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₂⟧ >> ⟦Γ₀∣R₂⟧⇒⟦τ×σ×κ⇒κ⟧ ⟩ >>
  elim
  where
    semStosetKey : SemStoset isStosetKey
    semStosetKey = ⟦ isStosetKey ⁑⟧

    semSemilatVal : SemSemilatCore l0 l0 l0 l0 l0 l0 l0 isSemilatVal
    semSemilatVal = ⟦ isSemilatVal ⁂⟧

    semSemilatTarget : SemSemilatCore l0 l0 l0 l0 l0 l0 l0 isSemilatTarget
    semSemilatTarget = ⟦ isSemilatTarget ⁂⟧

    T = SemStoset.T semStosetKey
    S = SemSemilatCore.S semSemilatVal
    targetS = SemSemilatCore.S semSemilatTarget

    τ▹σ-wf : IsPoset (τDict τKey τVal)
    τ▹σ-wf = τRes-wf Γ₀∣R₁⊢eDict∣τ▹σ

    τ-wf : IsPoset τKey
    τ-wf = stoset→poset isStosetKey

    σ-wf : IsPoset τVal
    σ-wf = semilat→poset isSemilatVal

    κ-wf : IsPoset τTarget
    κ-wf = semilat→poset isSemilatTarget

    ⟦Γ₀∣R₁⟧⇒⟦τ▹σ⟧ : ⟦ Γ₀ Γ∣ R₁ R⟧ ⇒ ⟦ DictPoset isStosetKey isSemilatVal ⁎⟧'  
    ⟦Γ₀∣R₁⟧⇒⟦τ▹σ⟧ rewrite (SemSemilatCore.US semSemilatVal) = 
      ⟦_⊢⟧ {τ₀-wf = DictPoset isStosetKey isSemilatVal} Γ₀∣R₁⊢eDict∣τ▹σ 

    ⟦τ∷σ∷κ∷Γ₀∣q₁∷q₂∷q₃∷R₂⟧⇒⟦κ⟧ : 
      ⟦ (τKey , τ-wf) ∷ (τVal , σ-wf) ∷ (τTarget , κ-wf) ∷ Γ₀ Γ∣ q₁ ∷ q₂ ∷ q₃ ∷ R₂ R⟧ ⇒ ⟦ κ-wf ⁎⟧'
    ⟦τ∷σ∷κ∷Γ₀∣q₁∷q₂∷q₃∷R₂⟧⇒⟦κ⟧ = ⟦_⊢⟧ {τ₀-wf = κ-wf} τ∷σ∷κ∷Γ₀∣q₁∷q₂∷q₃∷R₂⊢eBody∣κ

    ⟦+⟧⟦κ⟧⇒⟦q₃⟧⟦κ⟧ : (⟦ qMono q⟧ ⟦ κ-wf ⁎⟧') ⇒ (⟦ q₃ q⟧ ⟦ κ-wf ⁎⟧')    
    ⟦+⟧⟦κ⟧⇒⟦q₃⟧⟦κ⟧ = q≤⟦ q₃≤+ ⟧ ⟦ κ-wf ⁎⟧'   

    ⟦+⟧⟦σ⟧⇒⟦q₂⟧⟦σ⟧ : (⟦ qMono q⟧ ⟦ σ-wf ⁎⟧') ⇒ (⟦ q₂ q⟧ ⟦ σ-wf ⁎⟧')
    ⟦+⟧⟦σ⟧⇒⟦q₂⟧⟦σ⟧ = q≤⟦ q₂≤+ ⟧ ⟦ σ-wf ⁎⟧'

    ⟦?⟧⟦τ⟧⇒⟦q₁⟧⟦τ⟧ : (⟦ qAny q⟧ ⟦ τ-wf ⁎⟧') ⇒ (⟦ q₁ q⟧ ⟦ τ-wf ⁎⟧')
    ⟦?⟧⟦τ⟧⇒⟦q₁⟧⟦τ⟧ = q≤⟦ q≤? q₁ ⟧ ⟦ τ-wf ⁎⟧'

    ⟦τ∷σ∷κ∷Γ₀∣?∷+∷+∷R₂⟧⇒⟦κ∷σ∷τ∷Γ₀∣q₁∷q₂∷q₃∷R₂⟧ : 
      ⟦ (τKey , τ-wf) ∷ (τVal , σ-wf) ∷ (τTarget , κ-wf) ∷ Γ₀ Γ∣ qAny ∷ qMono ∷ qMono ∷ R₂ R⟧ ⇒
      ⟦ (τKey , τ-wf) ∷ (τVal , σ-wf) ∷ (τTarget , κ-wf) ∷ Γ₀ Γ∣ q₁ ∷ q₂ ∷ q₃ ∷ R₂ R⟧
    ⟦τ∷σ∷κ∷Γ₀∣?∷+∷+∷R₂⟧⇒⟦κ∷σ∷τ∷Γ₀∣q₁∷q₂∷q₃∷R₂⟧ = 
      ⟦?⟧⟦τ⟧⇒⟦q₁⟧⟦τ⟧ ⟨×⟩ (⟦+⟧⟦σ⟧⇒⟦q₂⟧⟦σ⟧ ⟨×⟩ (⟦+⟧⟦κ⟧⇒⟦q₃⟧⟦κ⟧ ⟨×⟩ id))
  
    ⟦τ∷σ∷κ∷Γ₀∣?∷+∷+∷R₂⟧⇒⟦κ⟧ : 
      ⟦ (τKey , τ-wf) ∷ (τVal , σ-wf) ∷ (τTarget , κ-wf) ∷ Γ₀ Γ∣ qAny ∷ qMono ∷ qMono ∷ R₂ R⟧ ⇒ ⟦ κ-wf ⁎⟧'
    ⟦τ∷σ∷κ∷Γ₀∣?∷+∷+∷R₂⟧⇒⟦κ⟧ = 
      ⟦τ∷σ∷κ∷Γ₀∣?∷+∷+∷R₂⟧⇒⟦κ∷σ∷τ∷Γ₀∣q₁∷q₂∷q₃∷R₂⟧ >> 
      ⟦τ∷σ∷κ∷Γ₀∣q₁∷q₂∷q₃∷R₂⟧⇒⟦κ⟧

    ⟦Γ₀∣R₂⟧⇒⟦τ×σ×κ⇒κ⟧ : 
      ⟦ Γ₀ Γ∣ R₂ R⟧ ⇒ (⇒-preorder (×-preorder (×-preorder (⟦ qAny q⟧ ⟦ τ-wf ⁎⟧') ⟦ σ-wf ⁎⟧') ⟦ κ-wf ⁎⟧') ⟦ κ-wf ⁎⟧')
    ⟦Γ₀∣R₂⟧⇒⟦τ×σ×κ⇒κ⟧ = Λ ( assoc (×-preorder (⟦ qAny q⟧ ⟦ τ-wf ⁎⟧') ⟦ σ-wf ⁎⟧') ⟦ κ-wf ⁎⟧' ⟦ Γ₀ Γ∣ R₂ R⟧ >>
                             assoc (⟦ qAny q⟧ ⟦ τ-wf ⁎⟧') ⟦ σ-wf ⁎⟧' (×-preorder ⟦ κ-wf ⁎⟧' ⟦ Γ₀ Γ∣ R₂ R⟧) >>
                             ⟦τ∷σ∷κ∷Γ₀∣?∷+∷+∷R₂⟧⇒⟦κ⟧)
    
    ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₁⟧ : ⟦ Γ₀ Γ∣ R₃ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₁ R⟧  
    ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₁⟧ rewrite eq = strengthenR Γ₀ (R₁ R+ R₂) R₁ (R≤R+S R₁ R₂)

    ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₂⟧ : ⟦ Γ₀ Γ∣ R₃ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₂ R⟧  
    ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₂⟧ rewrite eq = strengthenR Γ₀ (R₁ R+ R₂) R₂ (S≤R+S R₁ R₂)

    elim : 
      (×-preorder 
        ⟦ DictPoset isStosetKey isSemilatVal ⁎⟧'
        (⇒-preorder (×-preorder (×-preorder (⟦ qAny q⟧ ⟦ τ-wf ⁎⟧') ⟦ σ-wf ⁎⟧') ⟦ κ-wf ⁎⟧')
                                 ⟦ κ-wf ⁎⟧'))
      ⇒ (Poset.preorder ⟦ semilat→poset isSemilatTarget ⁎⟧)
    elim rewrite PE.sym (SemSemilatCore.US semSemilatVal) | PE.sym (SemSemilatCore.US semSemilatTarget) = 
      (▹-elim ⟦ τ-wf ⁎⟧ T (PE.sym $ SemStoset.eq semStosetKey) S targetS)
--]]]


⟦_⊢⟧ {τ₀-wf = PartialPoset σ-wf} (TyPure {n} {Γ₀} {R₀} {eBody} {σ} Γ₀∣R₀⊢eBody∣σ) =
  ⟦Γ₀∣R₀⟧⇒⟦σ⟧ >> pure ⟦ σ-wf ⁎⟧'
  where
    ⟦Γ₀∣R₀⟧⇒⟦σ⟧ : ⟦ Γ₀ Γ∣ R₀ R⟧ ⇒ ⟦ σ-wf ⁎⟧'
    ⟦Γ₀∣R₀⟧⇒⟦σ⟧ = ⟦_⊢⟧ {τ₀-wf = σ-wf} Γ₀∣R₀⊢eBody∣σ


⟦_⊢⟧ {τ₀-wf = PartialPoset τ₂-wf} 
      (TyMLet {n} {Γ₀} {R₁} {R₂} {R₃} {eq} {eFirst} {eAndThen} {τ₁} {τ₂} {τ₁-wf}  
              Γ₀∣R₁⊢eFirst∣τ₁ᵀ τ₁∷Γ₀∣+∷R₂⊢eAndThen∣τ₂ᵀ) =
  ⟨ ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₂⟧ >> ⟦Γ₀∣R₂⟧⇒⟦τ₁⇒τ₂ᵀ⟧ , ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₁⟧ >> ⟦Γ₀∣R₁⟧⇒⟦τ₁ᵀ⟧ ⟩ >> tstr >> ⇒ᵀ (⟨ π₂ , π₁ ⟩ >> ev) >> μ
  where
    τ₂ᵀ-wf≡τ₀-wf : (τRes-wf τ₁∷Γ₀∣+∷R₂⊢eAndThen∣τ₂ᵀ) ≡ (PartialPoset τ₂-wf)
    τ₂ᵀ-wf≡τ₀-wf = isPosetUnique (τRes-wf τ₁∷Γ₀∣+∷R₂⊢eAndThen∣τ₂ᵀ) (PartialPoset τ₂-wf)

    ⟦Γ₀∣R₁⟧⇒⟦τ₁ᵀ⟧ : ⟦ Γ₀ Γ∣ R₁ R⟧ ⇒ ⟦ PartialPoset τ₁-wf ⁎⟧'
    ⟦Γ₀∣R₁⟧⇒⟦τ₁ᵀ⟧ = ⟦_⊢⟧ {τ₀-wf = PartialPoset τ₁-wf} Γ₀∣R₁⊢eFirst∣τ₁ᵀ 

    ⟦τ₁∷Γ₀∣+∷R₂⟧⇒⟦τ₂ᵀ⟧ : ⟦ ((τ₁ , τ₁-wf) ∷ Γ₀) Γ∣ (qMono ∷ R₂) R⟧ ⇒ ⟦ PartialPoset τ₂-wf ⁎⟧'
    ⟦τ₁∷Γ₀∣+∷R₂⟧⇒⟦τ₂ᵀ⟧ rewrite τ₂ᵀ-wf≡τ₀-wf = ⟦_⊢⟧ {τ₀-wf = PartialPoset τ₂-wf} τ₁∷Γ₀∣+∷R₂⊢eAndThen∣τ₂ᵀ

    ⟦Γ₀∣R₂⟧⇒⟦τ₁⇒τ₂ᵀ⟧ : ⟦ Γ₀ Γ∣ R₂ R⟧ ⇒ (⇒-preorder ⟦ τ₁-wf ⁎⟧' ⟦ PartialPoset τ₂-wf ⁎⟧')
    ⟦Γ₀∣R₂⟧⇒⟦τ₁⇒τ₂ᵀ⟧ rewrite τ₂ᵀ-wf≡τ₀-wf = Λ ⟦τ₁∷Γ₀∣+∷R₂⟧⇒⟦τ₂ᵀ⟧ 

    ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₁⟧ : ⟦ Γ₀ Γ∣ R₃ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₁ R⟧ 
    ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₁⟧ rewrite eq = strengthenR Γ₀ (R₁ R+ R₂) R₁ (R≤R+S R₁ R₂)

    ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₂⟧ : ⟦ Γ₀ Γ∣ R₃ R⟧ ⇒ ⟦ Γ₀ Γ∣ R₂ R⟧ 
    ⟦Γ₀∣R₃⟧⇒⟦Γ₀∣R₂⟧ rewrite eq = strengthenR Γ₀ (R₁ R+ R₂) R₂ (S≤R+S R₁ R₂)

        
