module SemKinding where

open import Syntax
open import Kinding
open import BoolPoset
open import Relation.Binary
open import Data.Product
open import Level
open import Util using (l0;l1;l2)
open import Data.Unit renaming (preorder to unitPreorder ; decTotalOrder to unitToset )
open import Data.Nat as N
open import Data.Nat.Properties as NP
open import Data.Bool
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open Util

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

-- agda-mode: ⁎ is \asterisk, first choice
⟦_⁎⟧ : ∀ {τ : τ} → IsPoset τ → Preorder0
⟦ FunPoset {q = q} domIsProset codIsProset ⁎⟧ = 
  record{ 
    Carrier = D⇒C ;
    _≈_ = _≡_ ;
    _∼_ = _leq_ ;
    isPreorder = leqPreorder 
   }  
  where
    domProset : Preorder0
    domProset = ⟦ domIsProset ⁎⟧ 
    
    codProset : Preorder0
    codProset = ⟦ codIsProset ⁎⟧

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


⟦ UnitPoset ⁎⟧ = unitPreorder
⟦ BoolPoset ⁎⟧ = B≤-preorder
⟦ NatPoset ⁎⟧ = NP.≤-preorder


StrictTotalOrder0 : Set₁
StrictTotalOrder0 = StrictTotalOrder l0 l0 l0

-- agda-mode: ⁑ is \asterisk, second choice
⟦_⁑⟧ : ∀ {τ : τ} → IsToset τ → StrictTotalOrder0
⟦ UnitToset ⁑⟧ = UnitStrictTotal.⊤-strictTotalOrder
⟦ NatToset ⁑⟧ = {!!}
⟦ BoolToset ⁑⟧ = {!!}
⟦ ProductToset isTosetL isTosetR ⁑⟧ = {!!}
  where
    open StrictTotalOrder

    tosetL : StrictTotalOrder0
    tosetL = ⟦ isTosetL ⁑⟧

    tosetR : StrictTotalOrder0
    tosetR = ⟦ isTosetR ⁑⟧

    L : Set
    L = Carrier tosetL

    _ltL_ : L → L → Set
    _ltL_ = StrictTotalOrder._<_ tosetL

    _≈L_ : L → L → Set
    _≈L_ = StrictTotalOrder._≈_ tosetL

    R : Set
    R = Carrier tosetR

    _ltR_ : R → R → Set
    _ltR_ = StrictTotalOrder._<_ tosetR

    data _ltLR_ (x y : L × R) : Set where
      ltByLeft : (proj₁ x ltL proj₁ y) → (x ltLR y)
      ltByRight : (proj₁ x ≈L proj₁ y) → (proj₂ x ltR proj₂ y) → (x ltLR y)

    lt-isTransitive : Transitive _ltLR_
    lt-isTransitive {x} {y} {z} (ltByLeft x₁<y₁) (ltByLeft y₁<z₁) = ltByLeft ((trans tosetL) x₁<y₁ y₁<z₁)
    lt-isTransitive {(x₁ , _)} {(y₁ , _)} {(z₁ , _)} (ltByLeft x₁<y₁) (ltByRight y₁≈z₁ y₂<z₂) = ltByLeft x₁<z₁
      where
        x₁<z₁ : x₁ ltL z₁
        x₁<z₁ = (<-respʳ-≈ tosetL) y₁≈z₁ x₁<y₁
    lt-isTransitive {(x₁ , _)} {(y₁ , _)} {(z₁ , _)} (ltByRight x₁≈y₁ x₂<y₂) (ltByLeft y₁<z₁) = ltByLeft x₁<z₁
      where
        x₁<z₁ : x₁ ltL z₁
        x₁<z₁ = (<-respˡ-≈ tosetL) (IsEquivalence.sym (isEquivalence tosetL) x₁≈y₁) y₁<z₁
    lt-isTransitive {(x₁ , x₂)} {(y₁ , y₂)} {(z₁ , z₂)} (ltByRight x₁≈y₁ x₂<y₂) (ltByRight y₁≈z₁ y₂<z₂) = ltByRight x₁≈z₁ x₂<z₂
      where
        x₁≈z₁ : x₁ ≈L z₁
        x₁≈z₁ = IsEquivalence.trans (isEquivalence tosetL) x₁≈y₁ y₁≈z₁

        x₂<z₂ : x₂ ltR z₂
        x₂<z₂ = trans tosetR x₂<y₂ y₂<z₂

⟦ SumToset x x₁ ⁑⟧ = {!!}
