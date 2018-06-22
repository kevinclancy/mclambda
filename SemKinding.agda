module SemKinding where

open import Syntax
open import Kinding
open import BoolPoset
open import Relation.Binary
open import Data.Product
open import Level
open import Util using (l0;l1;l2)
open import Data.Unit renaming (preorder to unitPreorder)
open import Data.Nat as N
open import Data.Nat.Properties as NP
open import Data.Bool
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

-- record SemPoset {ℓ₁} : Set (suc ℓ₁) where
--   field
--     -- An agda type which serves represents a λMC type 
--     A : Set 
--     -- A partial order on A
--     _⊑_ : Rel A ℓ₁    
--     -- Proof that it's actually a partial order
--     isPartialOrder : IsPartialOrder _⊑_ 

Preorder0 : Set₁
Preorder0 = Preorder l0 l0 l0

open Preorder

⟦_⟧ : ∀ {τ : τ} → IsPoset τ → Preorder0
⟦ FunPoset {q = q} domIsProset codIsProset ⟧ = 
  record{ 
    Carrier = D⇒C ;
    _≈_ = _≡_ ;
    _∼_ = _leq_ ;
    isPreorder = leqPreorder 
   }  
  where
    domProset : Preorder0
    domProset = ⟦ domIsProset ⟧ 
    
    codProset : Preorder0
    codProset = ⟦ codIsProset ⟧

    D : Set
    D = Carrier domProset
    _d≈_ : D → D → Set
    _d≈_ = _≈_ domProset
    _d≤_ : D → D → Set
    _d≤_ = _∼_ domProset
    
    C : Set
    C = Carrier codProset
    _c≈_ : C → C → Set
    _c≈_ = _≈_ codProset
    _c≤_ : C → C → Set
    _c≤_ = _∼_ codProset
    isPreorderCod : IsPreorder _c≈_ _c≤_
    isPreorderCod = isPreorder codProset
    
    D⇒C : Set
    D⇒C = Σ[ f ∈ (D → C) ] (∀{v₁ v₂ : D} → v₁ d≤ v₂ → (f v₁) c≤ (f v₂))
    
    _leq_ : D⇒C → D⇒C → Set
    (f , _) leq (g , _) = ∀{v : D} → (f v) c≤ (g v) 
    
    isRefl : _≡_ ⇒ _leq_
    isRefl {(f , _)} PE.refl {v} = reflexiveCod fv≈fv
      where
        reflexiveCod : _c≈_ ⇒ _c≤_
        reflexiveCod = IsPreorder.reflexive isPreorderCod
        
        isEq≈ : IsEquivalence _c≈_ 
        isEq≈ = IsPreorder.isEquivalence isPreorderCod
        
        fv≈fv : (f v) c≈ (f v)
        fv≈fv = IsEquivalence.refl isEq≈ {f v}

    leqTransitive : Transitive _leq_
    leqTransitive {(f , _)} {(g , _)} {(h , _)} f≤g g≤h {v} = trans≤ fv≤gv gv≤hv 
      where
        fv≤gv : (f v) c≤ (g v)
        fv≤gv = f≤g {v}

        gv≤hv : (g v) c≤ (h v)
        gv≤hv = g≤h {v}

        trans≤ : Transitive _c≤_
        trans≤ = IsPreorder.trans isPreorderCod
        
    leqPreorder : IsPreorder _≡_ _leq_
    leqPreorder = 
      record{
         isEquivalence = PE.isEquivalence ;
         reflexive =  isRefl ;
         trans = (λ {i} → λ {j} → λ {k} → leqTransitive {i} {j} {k}) 
       }

⟦ UnitPoset ⟧ = unitPreorder
⟦ BoolPoset ⟧ = B≤-preorder
⟦ NatPoset ⟧ = NP.≤-preorder
