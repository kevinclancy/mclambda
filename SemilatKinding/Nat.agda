module SemilatKinding.Nat where

open import Relation.Nullary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary.Closure.ReflexiveTransitive
open import Data.Nat as N
open import Data.Nat.Properties as NP
open import Data.List
open import Data.List.Any
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
open import Data.Product
open import Data.Empty
open import Data.Sum
open import Data.Bool

open import Function using (_$_)

open import SemilatKinding.Core
open import Relation.Binary
open import Deltas
open import Level 
open import Syntax
open import Kinding
open import Util
open import FreeForgetfulAdjunction
open import BoolPoset
open import FinPoset
open import SemKinding

open import Data.Nat.Base as NB renaming (_⊔_ to _N⊔_)

semilatCore = ⟦ NatSemilat ⁂⟧ 

P : DeltaPoset {l0} {l0} {l0} {l0}
P = SemSemilatCore.P semilatCore

open DeltaPoset P
open import Data.List.Relation.Pointwise as PW
open import FreeSemilattice P renaming (SemilatCarrier to FP-Carrier ; ⊥ to ⊥ₚ ; _≈_ to _≈ₚ_ ; _∨_ to _∨ₚ_ ; ∷-Free to ∷-Free )

|f| : ℕ → FP-Carrier 
|f| zero = [] , []-Free 
|f| n@(suc n') = [ (n , (λ ())) ] , sng-free

|f|-≈ : (a b : ℕ) → (a ≡ b) → (|f| a ≈ₚ |f| b)
|f|-≈ a b a≡b@PE.refl = PW.refl (λ {x} → DeltaPoset.Eq.refl P {x})

|f|-⊥ : |f| 0 ≈ₚ ⊥ₚ
|f|-⊥ = []

|f|-∨ : (n0 n1 : ℕ) → |f| (n0 N.⊔ n1) ≈ₚ (|f| n0 ∨ₚ |f| n1)
|f|-∨ N.zero N.zero = []
|f|-∨ N.zero (N.suc n1) = PE.refl ∷ [] 
|f|-∨ (N.suc n0') N.zero = PE.refl ∷ []
|f|-∨ (N.suc n0') (N.suc n1') with n0' N.≤? n1' | n1' N.≤? n0'
|f|-∨ (N.suc n0') (N.suc n1') | yes n0'≤n1' | yes n1'≤n0' with NP.≤-antisym n0'≤n1' n1'≤n0'
|f|-∨ (N.suc n0') (N.suc n1') | yes n0'≤n1' | yes n1'≤n0' | PE.refl rewrite NP.⊔-idem n0' = PE.refl ∷ []
|f|-∨ (N.suc n0') (N.suc n1') | yes n0'≤n1' | no ¬n1'≤n0' rewrite m≤n⇒m⊔n≡n n0'≤n1' = PE.refl ∷ []
|f|-∨ (N.suc n0') (N.suc n1') | no ¬n0'≤n1' | yes n1'≤n0' rewrite m≤n⇒n⊔m≡n n1'≤n0' = PE.refl ∷ []
|f|-∨ (N.suc n0') (N.suc n1') | no ¬n0'≤n1' | no ¬n1'≤n0' with ≤-total n0' n1'
|f|-∨ (N.suc n0') (N.suc n1') | no ¬n0'≤n1' | no ¬n1'≤n0' | inj₁ n0'≤n1' = ⊥-elim $ ¬n0'≤n1' n0'≤n1'
|f|-∨ (N.suc n0') (N.suc n1') | no ¬n0'≤n1' | no ¬n1'≤n0' | inj₂ n1'≤n0' = ⊥-elim $ ¬n1'≤n0' n1'≤n0' 

|g| : FP-Carrier → ℕ 
|g| ([] , _) = 0
|g| ((n , _) ∷ [] , _) = n
|g| ((n , _) ∷ (m , _) ∷ _ , ∷-Free _ _ _ incomp _) = ⊥-elim $ incomp (here $ ≤-total n m)

|g|-≈ : (a b : FP-Carrier) → (a ≈ₚ b) → (|g| a ≡ |g| b)
|g|-≈ (.[] , snd) (.[] , snd₁) [] = PE.refl
|g|-≈ (ha ∷ [] , ∷-Free _ _ _ _ fta) (hb ∷ [] , ∷-Free _ _ _ _ ftb) (ha≡hb@PE.refl ∷ a≈b) = 
  PE.refl
|g|-≈ (ha1 ∷ ha2 ∷ _ , ∷-Free _ _ _ incomp _) (hb ∷ _ , ∷-Free _ _ _ _ _) =
  ⊥-elim $ incomp $ here $ ≤-total (proj₁ ha1) (proj₁ ha2)
|g|-≈ (ha ∷ [] , ∷-Free _ _ _ _ _) (hb1 ∷ hb2 ∷ _ , ∷-Free _ _ _ incomp _) =
  ⊥-elim $ incomp $ here $ ≤-total (proj₁ hb1) (proj₁ hb2)

|g|-⊥ : |g| ⊥ₚ ≡ 0
|g|-⊥ = PE.refl

|g|-∨ : (s1 s2 : FP-Carrier) → |g| (s1 ∨ₚ s2) ≡ (|g| s1) N.⊔ (|g| s2)
|g|-∨ ([] , f1) ([] , f2) = PE.refl
|g|-∨ ([] , f1) (h2 ∷ t2 , f2) = PE.refl
|g|-∨ c1@(h1 ∷ [] , f1) ([] , f2) rewrite ⊔-identityʳ (|g| c1) = PE.refl
|g|-∨ (h1 ∷ [] , ∷-Free _ _ _ _ _) (h2 ∷ [] , ∷-Free _ _ _ _ _) with h1 ∦? h2
|g|-∨ (h1 ∷ [] , ∷-Free _ _ _ _ _) (h2 ∷ [] , ∷-Free _ _ _ _ _) | l⊑r h1⊑h2 ¬h2⊑h1 = 
  PE.sym $ m≤n⇒m⊔n≡n h1⊑h2
|g|-∨ (h1 ∷ [] , ∷-Free _ _ _ _ _) (h2 ∷ [] , ∷-Free _ _ _ _ _) | r⊑l ¬h1⊑h2 h2⊑h1 = 
  PE.sym $ m≤n⇒n⊔m≡n h2⊑h1
|g|-∨ (h1 ∷ [] , ∷-Free _ _ _ _ _) (h2 ∷ [] , ∷-Free _ _ _ _ _) | l≈r h1≈h2 = 
  PE.sym $ m≤n⇒m⊔n≡n (⊑-reflexive {h1} {h2} h1≈h2)
|g|-∨ ((h1 , _) ∷ [] , ∷-Free _ _ _ _ _) ((h2 , _) ∷ [] , ∷-Free _ _ _ _ _) | l∥r h1∥h2 = 
  ⊥-elim $ h1∥h2 (NP.≤-total h1 h2)
|g|-∨ ((h11 , _) ∷ (h12 , _) ∷ _ , ∷-Free _ _ _ incomp _) (_ , _) =
  ⊥-elim $ incomp (here $ ≤-total h11 h12)
|g|-∨ (_ , _) ((h21 , _) ∷ (h22 , _) ∷ _ , ∷-Free _ _ _ incomp _) =
  ⊥-elim $ incomp (here $ ≤-total h21 h22)

inv-S→FP→S : (a : ℕ) → (|g| $ |f| a) ≡ a
inv-S→FP→S N.zero = PE.refl
inv-S→FP→S (N.suc a') = PE.refl

|FP| : Set
|FP| = BoundedJoinSemilattice.Carrier (FP P)

_≈FP_ : |FP| → |FP| → Set
_≈FP_ = BoundedJoinSemilattice._≈_ (FP P)

inv-FP→S→FP : (a : BoundedJoinSemilattice.Carrier (FP P)) → (|f| $ |g| a) ≈FP a  
inv-FP→S→FP a@([] , _) = PW.refl (λ {a} → PE.refl)
inv-FP→S→FP ((N.zero , ¬h≡0) ∷ [] , _) = ⊥-elim $ ¬h≡0 PE.refl
inv-FP→S→FP ((N.suc h , ¬h≡0) ∷ [] , _) = PE.refl ∷ []
inv-FP→S→FP ((a , ¬a≡0) ∷ (b , ¬b≡0) ∷ _ , ∷-Free _ _ _ incomp _) = 
  ⊥-elim $ incomp (here $ NP.≤-total a b) 

sem : SemSemilatIso l0 l0 l0 l0 l0 l0 l0 NatSemilat
sem = record
  { f = |f| , |f|-≈ , |f|-⊥ , |f|-∨
  ; g = |g| , |g|-≈ , |g|-⊥ , |g|-∨
  ; inv-S→FP→S = inv-S→FP→S
  ; inv-FP→S→FP = inv-FP→S→FP 
  }
