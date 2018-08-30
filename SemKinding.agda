module SemKinding where

open import Function using (_$_ ; _|>′_ ; const)
open import Function.Equivalence  
open import Function.Equality using (_⟨$⟩_) 
open import Syntax
open import Kinding
open import BoolPoset
open import Relation.Nullary
open import Relation.Binary
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.List
open import Data.List.Properties as LP
open import Data.List.Any as LAny
open import Data.List.All as LA
open import Level
open import Util using (l0;l1;l2)
open import Data.Unit renaming (preorder to unitPreorder ; decTotalOrder to unitToset) hiding (_≤_)
open import Data.Nat as N hiding (_<_ ; _⊔_)
open import Data.Nat.Properties as NP
open import Data.Bool
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
open import SemDeltaPoset
open import FreeForgetfulAdjunction
open import RelationalStructures
open Util

open Preorder
{-
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
-}

open import Relation.Binary.Lattice
open import Function.Inverse

record SemSemilat (cₛ ℓₛ₁ ℓₛ₂ cₚ ℓ⊑ₚ ℓ<ₚ ℓ~ₚ : Level) {τ τ₀ : τ} (isSemilat : IsSemilat τ τ₀)
                   : Set (Level.suc $ cₛ ⊔ ℓₛ₁ ⊔ ℓₛ₂ ⊔ cₚ ⊔ ℓ⊑ₚ ⊔ ℓ<ₚ ⊔ ℓ~ₚ) where
  field
    -- direct representation of semilattice
    S : BoundedJoinSemilattice cₛ ℓₛ₁ ℓₛ₂
    -- delta poset (freely generates S up-to-isomorphism)
    P : DeltaPoset {cₚ} {ℓ⊑ₚ} {ℓ<ₚ} {ℓ~ₚ}
    -- injection of τ₀ deltaPoset interpretation into P
    i : P ↣+ ⟦ semilat→delta isSemilat ⁑⟧ 
    -- factorization into free semilattice
    f : S ⇉ FP P
    -- defactorization out of free semilattice
    g : FP P ⇉ S
    -- f and g are inverses
    inv-S→FP→S : (a : BoundedJoinSemilattice.Carrier S) → (BoundedJoinSemilattice._≈_ S (proj₁ g $ proj₁ f $ a) a) 
    inv-FP→S→FP : (a : BoundedJoinSemilattice.Carrier $ FP P) → (BoundedJoinSemilattice._≈_ (FP P) (proj₁ f $ proj₁ g $ a) a) 

{-# TERMINATING #-}
⟦_⁂⟧ : ∀ {τ τ₀ : τ} → (isSemilat : IsSemilat τ τ₀) → SemSemilat l0 l0 l0 l0 l0 l0 l0 isSemilat   
{-
⟦_⁂⟧ NatSemilat = record
  { S = S
  ; P = P
  ; i = i
  ; f = |f| , |f|-≈ , |f|-⊥ , |f|-∨
  ; g = |g| , |g|-≈ , |g|-⊥ , |g|-∨
  ; inv-S→FP→S = inv-S→FP→S
  ; inv-FP→S→FP = inv-FP→S→FP 
  }
  where
    open import Data.Nat.Base as NB renaming (_⊔_ to _N⊔_)

    least : ∀ {m n : ℕ} → (z : ℕ) → (m ≤ z) → (n ≤ z) → (m N⊔ n ≤ z) 
    least {.0} {n} z z≤n n≤z = n≤z
    least {.(N.suc _)} {.0} .(N.suc _) (s≤s pm≤pz) z≤n = s≤s pm≤pz
    least {.(N.suc _)} {.(N.suc _)} .(N.suc _) (s≤s pm≤pz) (s≤s pn≤pz) = 
      let
        pm⊔pn≤pz = least _ pm≤pz pn≤pz 
      in 
        s≤s pm⊔pn≤pz
 
    S : BoundedJoinSemilattice l0 l0 l0
    S = record 
      { Carrier = ℕ
      ; _≈_ = _≡_
      ; _≤_ = N._≤_
      ; _∨_ = NB._⊔_
      ; ⊥ = N.zero
      ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
          { isPartialOrder = ≤-isPartialOrder
          ; supremum = λ x → λ y → (m≤m⊔n x y) , (n≤m⊔n x y) , least {x} {y}
          }
        ; minimum = λ n → N.z≤n {n} 
        } 
      }

    P : DeltaPoset {l0} {l0} {l0} {l0} 
    P = record
      { Carrier = Σ[ n ∈ ℕ ] ¬ (n ≡ 0)
      ; _⊑_ = _⊑₀_
      ; _<_ = _<₀_
      ; _≈_ = _≈₀_
      ; isStrictTotalOrder = isStrictTotalOrder₀
      ; isDecPartialOrder = isDecPartialOrder₀
      ; unimodality = λ {a} → λ {b} → λ {c} → unimodality {a} {b} {c}
      }
      where
        deltaPosetℕ = ⟦ NatDelta ⁑⟧ 
        
        C = Σ[ n ∈ ℕ ] ¬ (n ≡ 0)
        
        _⊑₀_ : C → C → Set _
        (n1 , p1) ⊑₀ (n2 , p2) = n1 N.≤ n2

        _<₀_ : C → C → Set _
        (n1 , p1) <₀ (n2 , p2) = n1 N.< n2

        _≈₀_ : C → C → Set _
        (n1 , p1) ≈₀ (n2 , p2) = n1 ≡ n2

        _∦₀_ : C → C → Set
        a ∦₀ b = a ⊑₀ b ⊎ b ⊑₀ a

        _∥₀_ : C → C → Set
        a ∥₀ b = ¬ (a ∦₀ b)
        
        unimodality : {a b c : C} → (a <₀ b) → (b <₀ c) → (a ∥₀ b) → (b ∥₀ c) → (a ∥₀ c)
        unimodality = DeltaPoset.unimodality ⟦ NatDelta ⁑⟧ 

        <₀-compare : Trichotomous _≈₀_ _<₀_
        <₀-compare (a , _) (b , _) = <-cmp a b

        ⊑₀-reflexive : _≈₀_ ⇒ _⊑₀_
        ⊑₀-reflexive {a , _} {b , _} a≈b = ≤-reflexive {a} {b} a≈b

        isEquiv₀ : IsEquivalence _≈₀_
        isEquiv₀ = record
          { refl = PE.refl
          ; sym = PE.sym
          ; trans = PE.trans
          }

        _≟₀_ : Decidable _≈₀_
        (a , _) ≟₀ (b , _) = a N.≟ b

        _⊑₀?_ : Decidable _⊑₀_
        (a , _) ⊑₀? (b , _) = a N.≤? b

        isStrictTotalOrder₀ : IsStrictTotalOrder _≈₀_ _<₀_
        isStrictTotalOrder₀ = record
          { isEquivalence = isEquiv₀
          ; trans = <-trans
          ; compare = <₀-compare
          }

        isDecPartialOrder₀ : IsDecPartialOrder _≈₀_ _⊑₀_
        isDecPartialOrder₀ = record
          { isPartialOrder = record
            { isPreorder = record
                { isEquivalence = isEquiv₀
                ; reflexive = λ {a} → λ {b} → ⊑₀-reflexive {a} {b}
                ; trans = ≤-trans
                }
            ; antisym = ≤-antisym
            }
          ; _≟_ = _≟₀_
          ; _≤?_ = _⊑₀?_
          }

    |i| : (DeltaPoset.Carrier P) → (DeltaPoset.Carrier ⟦ NatDelta ⁑⟧)
    |i| (n , p) = n

    |i|-monotone : Monotone P ⟦ NatDelta ⁑⟧ |i|
    |i|-monotone {n , _} {n' , _} n⊑n' = n⊑n'
      
    |i|-monic : Injective (DeltaPoset.≈-setoid P) (DeltaPoset.≈-setoid ⟦ NatDelta ⁑⟧) |i|
    |i|-monic {a , _} {a' , _} fa≈fa' = fa≈fa' 

    i : P ↣+ ⟦ NatDelta ⁑⟧
    i = (|i| , (λ {a} → λ {a'} → |i|-monotone {a} {a'}) , (λ {a} → λ {a'} → |i|-monic {a} {a'}))

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
⟦ BoolSemilat ⁂⟧ = record
  { S = S
  ; P = P
  ; i = |i| , |i|-monotone , |i|-monic
  ; f = |f| , |f|-≈ , |f|-⊥ , |f|-∨
  ; g = |g| , |g|-≈ , |g|-⊥ , |g|-∨
  ; inv-S→FP→S = inv-S→FP→S
  ; inv-FP→S→FP = inv-FP→S→FP 
  }
  where
    open import Data.Bool
    open import BoolPoset
    open import FinPoset
    open import Relation.Binary.Closure.ReflexiveTransitive
    open UnitStrictTotal
    open import UnitPoset

    lowerˡ : ∀ (a b : Bool) → a B≤ a B∨ b
    lowerˡ false false = ε
    lowerˡ false true = (here $ PE.refl , PE.refl) ◅ ε
    lowerˡ true false = ε
    lowerˡ true true = ε

    lowerʳ : ∀ (a b : Bool) → b B≤ a B∨ b
    lowerʳ false false = ε
    lowerʳ false true = ε
    lowerʳ true false = (here $ PE.refl , PE.refl) ◅ ε
    lowerʳ true true = ε
    
    least : ∀ (a b : Bool) → (z : Bool) → (a B≤ z) → (b B≤ z) → (a B∨ b B≤ z) 
    least false false false a≤z b≤z = ε
    least false false true a≤z b≤z = (here $ PE.refl , PE.refl) ◅ ε
    least false true false a≤z (here () ◅ _)
    least false true false a≤z (there () ◅ _)
    least false true true a≤z b≤z = ε
    least true false false (here () ◅ _) b≤z
    least true false false (there () ◅ _) b≤z
    least true false true a≤z b≤z = ε
    least true true false (here () ◅ _) b≤z
    least true true false (there () ◅ _) b≤z
    least true true true a≤z b≤z = ε

    minimum : Minimum _B≤_ false
    minimum false = ε
    minimum true = (here $ PE.refl , PE.refl) ◅ ε

    S : BoundedJoinSemilattice l0 l0 l0
    S = record 
      { Carrier = Bool
      ; _≈_ = _≡_
      ; _≤_ = _B≤_
      ; _∨_ = _B∨_ 
      ; ⊥ = false
      ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
          { isPartialOrder = B≤-isPartialOrder
          ; supremum =  λ x → λ y → lowerˡ x y , lowerʳ x y , least x y
          }
        ; minimum = minimum 
        } 
      }

    P : DeltaPoset {l0} {l0} {l0} {l0}
    P = ⟦ UnitDelta ⁑⟧ 

    |i| : (DeltaPoset.Carrier P) → (DeltaPoset.Carrier ⟦ UnitDelta ⁑⟧)
    |i| tt = tt

    |i|-monotone : Monotone P ⟦ UnitDelta ⁑⟧ |i|
    |i|-monotone {tt} {tt} tt⊑tt = ε
      
    |i|-monic : Injective (DeltaPoset.≈-setoid P) (DeltaPoset.≈-setoid ⟦ UnitDelta ⁑⟧) |i|
    |i|-monic {tt} {tt} _ = PE.refl 

    open DeltaPoset P
    open import Data.List.Relation.Pointwise as PW
    open import FreeSemilattice P renaming (⊥ to F⊥ ; _∨_ to _F∨_ ; _≈_ to _F≈_ )
    open import Data.List.Any.Properties
    open import Data.List.All

    |f| : Bool → Σ[ l ∈ List ⊤ ] (IsFreeList l)
    |f| false = [] , []-Free
    |f| true = tt ∷ [] , (∷-Free tt [] [] ¬Any[] []-Free) 

    |f|-≈ : (a b : Bool) → (a ≡ b) → (|f| a) F≈ (|f| b)
    |f|-≈ a b a≡b@PE.refl = PW.refl PE.refl

    |f|-⊥ : |f| false F≈ F⊥ 
    |f|-⊥ = PW.refl PE.refl

    |f|-∨ : (a b : Bool) → |f| (a B∨ b) F≈ (|f| a F∨ |f| b)
    |f|-∨ false false = PW.refl PE.refl
    |f|-∨ false true = PW.refl PE.refl
    |f|-∨ true false = PW.refl PE.refl
    |f|-∨ true true = PW.refl PE.refl

    |g| : Σ[ l ∈ List ⊤ ] (IsFreeList l) → Bool
    |g| ([] , []-Free) = false
    |g| (tt ∷ [] , ∷-Free _ _ _ _ _) = true
    |g| (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) = 
      ⊥-elim $ incomp (here (inj₁ $ DeltaPoset.reflexive P PE.refl))

    |g|-≈ : (a b : SemilatCarrier) → a F≈ b → (|g| a) ≡ (|g| b)
    |g|-≈ (.[] , []-Free) (.[] , []-Free) [] = PE.refl
    |g|-≈ (ha ∷ [] , ∷-Free _ _ _ _ _) (hb ∷ [] , ∷-Free _ _ _ _ _) (ha≡hb ∷ []) = PE.refl
    |g|-≈ (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) _ (ha≡hb ∷ _) = 
      ⊥-elim $ incomp $ here $ inj₁ (IsDecPartialOrder.refl ⊤≤-isDecPartialOrder)
    |g|-≈ _ (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) (ha≡hb ∷ _) =
      ⊥-elim $ incomp $ here $ inj₁ (IsDecPartialOrder.refl ⊤≤-isDecPartialOrder)

    |g|-⊥ : |g| F⊥ ≡ false 
    |g|-⊥ = PE.refl

    |g|-∨ : (a b : Σ[ l ∈ List ⊤ ] IsFreeList l) → (|g| (a F∨ b) ≡ (|g| a) B∨ (|g| b))
    |g|-∨ ([] , []-Free) ([] , []-Free) = PE.refl
    |g|-∨ (tt ∷ [] , ∷-Free _ _ _ _ _) ([] , []-Free) = PE.refl 
    |g|-∨ ([] , []-Free) (tt ∷ [] , ∷-Free _ _ _ _ _) = PE.refl
    |g|-∨ (tt ∷ [] , ∷-Free _ _ _ _ _) (tt ∷ [] , ∷-Free _ _ _ _ _) = PE.refl
    |g|-∨ (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) _ = ⊥-elim $ incomp $ here (inj₁ $ DeltaPoset.reflexive P PE.refl) 
    |g|-∨ _ (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) = ⊥-elim $ incomp $ here (inj₁ $ DeltaPoset.reflexive P PE.refl)

    inv-S→FP→S : (a : Bool) → (|g| $ |f| a) ≡ a
    inv-S→FP→S true = PE.refl
    inv-S→FP→S false = PE.refl

    inv-FP→S→FP : (a : Σ[ l ∈ List ⊤ ] IsFreeList l) → (|f| $ |g| a) F≈ a 
    inv-FP→S→FP ([] , []-Free) = PW.refl PE.refl
    inv-FP→S→FP (tt ∷ [] , ∷-Free _ _ _ _ _) = PW.refl PE.refl
    inv-FP→S→FP (tt ∷ tt ∷ _ , ∷-Free _ _ _ incomp _) = ⊥-elim $ incomp $ here (inj₁ $ DeltaPoset.reflexive P PE.refl)
-}
{-
⟦ DictSemilat domIsToset codIsSemilat ⁂⟧ = record
  { S = {!!}
  ; P = {!!}
  ; i = {!!} , {!!} , {!!}
  ; f = {!!} , {!!} , {!!}
  ; g = {!!} , {!!} , {!!}
  ; inv-S→FP→S = {!!}
  ; inv-FP→S→FP = {!!} 
  }
  where
    open import Data.List.Relation.Pointwise as LPW
    open import Data.Product.Relation.Pointwise.NonDependent as PPW
    open import Data.List.All as LAll
    open import Data.List.Any as LAny
    open import Data.Product
 
    tosetDom = ⟦ domIsToset T⟧
    semSemilatCod = ⟦ codIsSemilat ⁂⟧
    bjsCod = SemSemilat.S semSemilatCod
    |D| = StrictTotalOrder.Carrier tosetDom
    |C| = BoundedJoinSemilattice.Carrier (SemSemilat.S semSemilatCod)

    open StrictTotalOrder tosetDom renaming (_≈_ to _≈d_ ; _<_ to _<d_ ; compare to compare-d)
    open BoundedJoinSemilattice bjsCod renaming (_≈_ to _≈c_ ; _≤_ to _≤c_ ; ⊥ to ⊥c )

    Elem : Set
    Elem = Σ[ d↦c ∈ |D| × |C| ] ¬ ((proj₂ d↦c) ≈c ⊥c) 

    _≈Elem_ : Elem → Elem → Set
    ((d1 , c1) , _) ≈Elem ((d2 , c2) , _) = (d1 ≈d d2) × (c1 ≈c c2) 

    data Sorted : List Elem → Set where
      []-Sorted : Sorted []
      ∷-Sorted : {h : Elem} → (t : List Elem) → 
                  (min : All {A = Elem} (λ e → ((proj₁ $ proj₁ h) <d (proj₁ $ proj₁ e))) t) →
                  (s : Sorted t) → Sorted (h ∷ t)

    Carrier' : Set
    Carrier' = Σ[ l ∈ List Elem ] (Sorted l)
    
    _≈'_ : Carrier' → Carrier' → Set
    (l1 , _) ≈' (l2 , _) =  LPW.Pointwise _≈Elem_ l1 l2  

    infix 4 _≤'_ 

    {-
    data _≤'_ : Carrier' → Carrier' → Set where
      ≤'-[] : [] ≤' []
      ≤'-skip : (d1 d2 : |D|) → (c1 c2 : |C|) → (t1 t2 : Carrier') → (d2 < d1) → 
                ((d1 , c1) ∷ t1 ≤' t2) → ((d1 , c1) ∷ t1 ≤' (d2 , c2) ∷ t2)
      ≤'-cmp : (d1 d2 : |D|) → (c1 c2 : |C|) → (t1 t2 : Carrier') → (d1 ≈ d2) → 
    -}

    _≤'_ : Carrier' → Carrier' → Set
    (l1 , _) ≤' (l2 , _)  = All (λ x → (Any (f x) l2)) l1
      where
        f : Elem → Elem → Set
        f ((d1 , c1) , _) ((d2 , c2) , _) = (d1 ≈d d2) × (c1 ≤c c2)

    _∨'_ : Carrier' → Carrier' → Carrier'
    ([] , _) ∨' ([] , _) = [] , []-Sorted
    ([] , _) ∨' ((h2 ∷ t2) , ∷-Sorted t2 min2 st2) = (h2 ∷ t2) , ∷-Sorted t2 min2 st2
    (h1 ∷ t1 , ∷-Sorted t1 min1 st1) ∨' ([] , []-Sorted) = h1 ∷ t1 , ∷-Sorted t1 min1 st1
    (((d1 , c1) , _) ∷ t1 , ∷-Sorted t1 min1 st1) ∨' (((d2 , c2) , _) ∷ t2 , ∷-Sorted t2 min2 st2) with compare-d d1 d2 
    (((d1 , c1) , _) ∷ t1 , ∷-Sorted t1 min1 st1) ∨' b@(((d2 , c2) , _) ∷ t2 , ∷-Sorted t2 min2 st2) | tri< d1<d2 _ _ =
      let 
        rec : Carrier'
        rec = (t1 , st1) ∨' b
        
        -- min12 : 
      in
      {!!}
    (((d1 , c1) , _) ∷ t1 , ∷-Sorted t1 min1 st1) ∨' (((d2 , c2) , _) ∷ t2 , ∷-Sorted t2 min2 st2) | tri≈ _ d1≈d2 _ =
      {!!}
    (((d1 , c1) , _) ∷ t1 , ∷-Sorted t1 min1 st1) ∨' (((d2 , c2) , _) ∷ t2 , ∷-Sorted t2 min2 st2) | tri> _ _ d2<d1 =
      {!!}

    S : BoundedJoinSemilattice l0 l0 l0
    S = record 
      { Carrier = Carrier' 
      ; _≈_ = _≈'_ 
      ; _≤_ = _≤'_
      ; _∨_ = {!!} 
      ; ⊥ = {!!}
      ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
          { isPartialOrder = {!!}
          ; supremum =  {!!}
          }
        ; minimum = {!!} 
        } 
      }
-}

⟦ ProductSemilat isSemilatL isSemilatR ⁂⟧ = record
  { S = S
  ; P = P
  ; i = |i| , |i|-mono , |i|-injective
  ; f = {!!} -- |f| , |f|-≈ , |f|-⊥ , |f|-∨  -- |f| , |f|-⊥ , |f|-∨
  ; g = {!!} -- |g| , |g|-≈ , |g|-⊥ , |g|-∨
  ; inv-S→FP→S = {!!}
  ; inv-FP→S→FP = {!!} 
  }
  where
    open import Data.Product.Relation.Pointwise.NonDependent as PW
    open import Data.Sum.Relation.Core
    open import Data.List.All
    open import Data.Sum
    open import Data.List.Relation.Pointwise as LPW hiding (Rel ; Pointwise)

    semSemilatL = ⟦ isSemilatL ⁂⟧
    semSemilatR = ⟦ isSemilatR ⁂⟧

    bjsL = SemSemilat.S semSemilatL
    bjsR = SemSemilat.S semSemilatR

    |L| = BoundedJoinSemilattice.Carrier bjsL
    |R| = BoundedJoinSemilattice.Carrier bjsR

    _≈L_ = BoundedJoinSemilattice._≈_ bjsL
    ≈L-refl = BoundedJoinSemilattice.Eq.refl bjsL
    ≈L-sym = BoundedJoinSemilattice.Eq.sym bjsL
    ≈L-setoid : Setoid _ _
    ≈L-setoid = record
      { Carrier = |L|
      ; isEquivalence = BoundedJoinSemilattice.isEquivalence bjsL
      }
    _≈R_ = BoundedJoinSemilattice._≈_ bjsR
    ≈R-refl = BoundedJoinSemilattice.Eq.refl bjsR
    ≈R-sym = BoundedJoinSemilattice.Eq.sym bjsR
    ≈R-setoid : Setoid _ _
    ≈R-setoid = record
      { Carrier = |R|
      ; isEquivalence = BoundedJoinSemilattice.isEquivalence bjsR
      }
    _≤L_ = BoundedJoinSemilattice._≤_ bjsL
    _≤R_ = BoundedJoinSemilattice._≤_ bjsR

    _∨L_ = BoundedJoinSemilattice._∨_ bjsL
    _∨R_ = BoundedJoinSemilattice._∨_ bjsR

    ⊥L = BoundedJoinSemilattice.⊥ bjsL
    ⊥R = BoundedJoinSemilattice.⊥ bjsR

    Carrier' : Set
    Carrier' = |L| × |R| 

    infixr 4 _∨'_
    infix 5 _≤'_
    infix 6 _≈'_

    _≈'_ : Rel Carrier' _
    _≈'_ = Pointwise _≈L_ _≈R_

    _≤'_ : Rel Carrier' _
    _≤'_ = Pointwise _≤L_ _≤R_

    _∨'_ : Carrier' → Carrier' → Carrier'
    (aL , aR) ∨' (bL , bR) = (aL ∨L bL) , (aR ∨R bR) 

    ⊥' : Carrier'
    ⊥' = (⊥L , ⊥R)

    minimum' : (z : Carrier') → ⊥' ≤' z
    minimum' (zL , zR) = BoundedJoinSemilattice.minimum bjsL zL , BoundedJoinSemilattice.minimum bjsR zR

    lowerL : (a b : Carrier') → a ≤' (a ∨' b)
    lowerL a@(aL , aR) b@(bL , bR) =
      let
        lowerL-L , _ , _ = BoundedJoinSemilattice.supremum bjsL aL bL 
        lowerL-R , _ , _ = BoundedJoinSemilattice.supremum bjsR aR bR
      in
      lowerL-L , lowerL-R

    lowerR : (a b : Carrier') → b ≤' (a ∨' b)
    lowerR a@(aL , aR) b@(bL , bR) =
      let
        _ , lowerR-L , _ = BoundedJoinSemilattice.supremum bjsL aL bL 
        _ , lowerR-R , _ = BoundedJoinSemilattice.supremum bjsR aR bR
      in
      lowerR-L , lowerR-R

    upper : (a b z : Carrier') → (a ≤' z) → (b ≤' z) → ((a ∨' b) ≤' z)
    upper a@(aL , aR) b@(bL , bR) z@(zL , zR) (aL≤zL ,  aR≤zR) (bL≤zL , bR≤zR) =
      let
        _ , _ , sup-L = BoundedJoinSemilattice.supremum bjsL aL bL 
        _ , _ , sup-R = BoundedJoinSemilattice.supremum bjsR aR bR
      in
      sup-L zL aL≤zL bL≤zL , sup-R zR aR≤zR bR≤zR 

    S : BoundedJoinSemilattice l0 l0 l0
    S = record 
      { Carrier = Carrier' 
      ; _≈_ = _≈'_
      ; _≤_ = _≤'_
      ; _∨_ = _∨'_ 
      ; ⊥ = ⊥'
      ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
          { isPartialOrder = ×-isPartialOrder (BoundedJoinSemilattice.isPartialOrder bjsL)
                                              (BoundedJoinSemilattice.isPartialOrder bjsR)
          ; supremum = λ x → λ y → lowerL x y , lowerR x y , upper x y
          }
        ; minimum = minimum' 
        } 
      }

    joinSemilatticeS : JoinSemilattice l0 l0 l0
    joinSemilatticeS = BoundedJoinSemilattice.joinSemiLattice S

    ≈'-refl = BoundedJoinSemilattice.Eq.refl S
    ≈'-sym = BoundedJoinSemilattice.Eq.sym S

    ≈'-setoid : Setoid _ _
    ≈'-setoid = record
      { Carrier = Carrier'
      ; isEquivalence = ×-isEquivalence (BoundedJoinSemilattice.isEquivalence bjsL) (BoundedJoinSemilattice.isEquivalence bjsR)
      }

    deltaL = SemSemilat.P semSemilatL
    deltaR = SemSemilat.P semSemilatR

    |L₀| = DeltaPoset.Carrier deltaL
    |R₀| = DeltaPoset.Carrier deltaR
  
    Carrier₀ = |L₀| ⊎ |R₀|  

    _≈L₀_ : |L₀| → |L₀| → Set  
    _≈L₀_ = DeltaPoset._≈_ deltaL
    ≈L₀-sym = DeltaPoset.sym≈ deltaL
    ≈L₀-refl = DeltaPoset.refl≈ deltaL
    ≈L₀-reflexive = DeltaPoset.reflexive≈ deltaL
    ≈L₀-trans = DeltaPoset.trans≈ deltaL
    ≈L₀-setoid : Setoid _ _
    ≈L₀-setoid = record
      { Carrier = |L₀|
      ; isEquivalence = DeltaPoset.Eq.isEquivalence deltaL
      }
    _≈R₀_ : |R₀| → |R₀| → Set
    _≈R₀_ = DeltaPoset._≈_ deltaR
    ≈R₀-sym = DeltaPoset.sym≈ deltaR
    ≈R₀-refl = DeltaPoset.refl≈ deltaR
    ≈R₀-reflexive = DeltaPoset.reflexive≈ deltaR
    ≈R₀-trans = DeltaPoset.trans≈ deltaR
    ≈R₀-setoid : Setoid _ _
    ≈R₀-setoid = record
      { Carrier = |R₀|
      ; isEquivalence = DeltaPoset.Eq.isEquivalence deltaR
      }
    _⊑L₀_ : |L₀| → |L₀| → Set
    _⊑L₀_ = DeltaPoset._⊑_ deltaL
    _⊑R₀_ : |R₀| → |R₀| → Set
    _⊑R₀_ = DeltaPoset._⊑_ deltaR
    _∥L₀_ : |L₀| → |L₀| → Set
    _∥L₀_ = DeltaPoset._∥_ deltaL
    _∥R₀_ : |R₀| → |R₀| → Set
    _∥R₀_ = DeltaPoset._∥_ deltaR
    _∦L₀_ : |L₀| → |L₀| → Set
    _∦L₀_ = DeltaPoset._∦_ deltaL
    _∦L₀?_ = DeltaPoset._∦?_ deltaL
    _∦R₀_ : |R₀| → |R₀| → Set
    _∦R₀_ = DeltaPoset._∦_ deltaR
    _∦R₀?_ = DeltaPoset._∦?_ deltaR
    _<L₀_ : |L₀| → |L₀| → Set
    _<L₀_ = DeltaPoset._<_ deltaL
    <L₀-trans = DeltaPoset.trans< deltaL
    irreflL₀ = DeltaPoset.irrefl deltaL
    compareL₀ = DeltaPoset.compare deltaL
    _<R₀_ : |R₀| → |R₀| → Set
    _<R₀_ = DeltaPoset._<_ deltaR
    <R₀-trans = DeltaPoset.trans< deltaR
    irreflR₀ = DeltaPoset.irrefl deltaR
    compareR₀ = DeltaPoset.compare deltaR
    unimL = DeltaPoset.unimodality deltaL
    unimR = DeltaPoset.unimodality deltaR

    P : DeltaPoset {l0} {l0} {l0} {l0}
    P = sumDeltaPoset
      where
        open import SumDelta deltaL deltaR

    |P| : Set
    |P| = DeltaPoset.Carrier P

    _≈P_ : |P| → |P| → Set
    _≈P_ = DeltaPoset._≈_ P
    
    ≈P-setoid : Setoid _ _
    ≈P-setoid = DeltaPoset.≈-setoid P
    ≈P-reflexive = DeltaPoset.Eq.reflexive P
    ≈P-refl = DeltaPoset.Eq.refl P
    ≈P-trans = DeltaPoset.Eq.trans P

    _<P_ : |P| → |P| → Set
    _<P_ = DeltaPoset._<_ P

    _⊑P_ : |P| → |P| → Set
    _⊑P_ = DeltaPoset._⊑_ P

    _∦P_ : |P| → |P| → Set
    _∦P_ = DeltaPoset._∦_ P

    _∦P?_ = DeltaPoset._∦?_ P
    compareP = DeltaPoset.compare P
    
    ∦P-sym = DeltaPoset.∦-sym P

    _∥P_ : |P| → |P| → Set
    _∥P_ = DeltaPoset._∥_ P

    iL : (SemSemilat.P semSemilatL) ↣+ ⟦ semilat→delta isSemilatL ⁑⟧ 
    iL = SemSemilat.i semSemilatL

    |iL| : DeltaPoset.Carrier (SemSemilat.P semSemilatL) → DeltaPoset.Carrier ⟦ semilat→delta isSemilatL ⁑⟧ 
    |iL| = proj₁ iL

    iL-mono : Monotone (SemSemilat.P semSemilatL) ⟦ semilat→delta isSemilatL ⁑⟧ |iL|
    iL-mono = proj₁ $ proj₂ iL

    iL-injective : Injective (DeltaPoset.≈-setoid deltaL) (DeltaPoset.≈-setoid $ ⟦ semilat→delta isSemilatL ⁑⟧) |iL|
    iL-injective = proj₂ $ proj₂ iL

    iR : (SemSemilat.P semSemilatR) ↣+ ⟦ semilat→delta isSemilatR ⁑⟧ 
    iR = SemSemilat.i semSemilatR

    |iR| : DeltaPoset.Carrier (SemSemilat.P semSemilatR) → DeltaPoset.Carrier ⟦ semilat→delta isSemilatR ⁑⟧ 
    |iR| = proj₁ iR

    iR-mono : Monotone (SemSemilat.P semSemilatR) ⟦ semilat→delta isSemilatR ⁑⟧ |iR|
    iR-mono = proj₁ $ proj₂ iR

    iR-injective : Injective (DeltaPoset.≈-setoid deltaR) (DeltaPoset.≈-setoid $ ⟦ semilat→delta isSemilatR ⁑⟧) |iR|
    iR-injective = proj₂ $ proj₂ iR
     
    |i| : DeltaPoset.Carrier P → DeltaPoset.Carrier ⟦ semilat→delta $ ProductSemilat isSemilatL isSemilatR ⁑⟧ 
    |i| = [_,_] (λ x → x |>′ |iL| |>′ inj₁) (λ x → x |>′ |iR| |>′ inj₂)

    |i|-mono : Monotone P ⟦ semilat→delta $ ProductSemilat isSemilatL isSemilatR ⁑⟧ |i|
    |i|-mono {inj₁ a'} {inj₁ b'} (₁∼₁ a'⊑b') = ₁∼₁ $ iL-mono a'⊑b'
    |i|-mono {inj₁ a'} {inj₂ b'} (₁∼₂ ())
    |i|-mono {inj₂ a'} {inj₁ x} ()
    |i|-mono {inj₂ a'} {inj₂ b'} (₂∼₂ a'⊑b') = ₂∼₂ $ iR-mono a'⊑b'

    |i|-injective : Injective (DeltaPoset.≈-setoid P) (DeltaPoset.≈-setoid ⟦ semilat→delta $ ProductSemilat isSemilatL isSemilatR ⁑⟧) |i|
    |i|-injective {inj₁ a'} {inj₁ b'} (₁∼₁ ia'≈ib') = ₁∼₁ $ iL-injective ia'≈ib'
    |i|-injective {inj₁ a'} {inj₂ b'} (₁∼₂ ())
    |i|-injective {inj₂ a'} {inj₁ b'} ()
    |i|-injective {inj₂ a'} {inj₂ b'} (₂∼₂ ia'≈ib') = ₂∼₂ $ iR-injective ia'≈ib'

    open import FreeSemilattice P renaming 
      (⊥ to ⊥F ; _∨_ to _∨F_ ; _≈_ to _≈F_ ; _~_ to _~F_ ; ≈-refl to ≈F-refl ; SemilatCarrier to Carrier-FP ;
       ≈-reflexive to ≈F-reflexive ; FP-BJS to FP-BJS ; ∨-identityˡ to ∨F-identityˡ ; ∨-identityʳ to ∨F-identityʳ ; 
       ≈-sym to ≈F-sym ; ∨-congˡ to ∨F-congˡ ; ∨-congʳ to ∨F-congʳ ; ∨-assoc to ∨F-assoc ; ∨-comm to ∨F-comm ;
       _∈_ to _∈P_ ; _∈'_ to _∈P'_ ; FP-setoid to FP-setoid ) 
    open import FreeSemilattice deltaL renaming 
      (IsFreeList to IsFreeListL ; []-Free to []-FreeL ; ∷-Free to ∷-FreeL ; _≈_ to _≈FL_ ; ⊥ to ⊥FL ; 
       SemilatCarrier to Carrier-FPL ; _∨_ to _∨FL_ ; FP-BJS to FPL-BJS ; FP-setoid to FPL-setoid ;
       ∨-identityˡ to ∨FL-identityˡ ; ∨-identityʳ to ∨FL-identityʳ ; ⊑-refl to ⊑L₀-refl ; ⊑-reflexive to ⊑L₀-reflexive ;
       sng-free to sng-freeL ; _≤_ to _≤FL_ ; ≈-sym to ≈FL-sym ; _∈_ to _∈L_ ; _∈'_ to _∈L'_ ;
       c1≈c2⇔sameElements to c1≈c2⇔sameElementsL )
    open import FreeSemilattice deltaR renaming 
      (IsFreeList to IsFreeListR ; []-Free to []-FreeR ; ∷-Free to ∷-FreeR ; _≈_ to _≈FR_ ; ⊥ to ⊥FR ; 
       SemilatCarrier to Carrier-FPR ; _∨_ to _∨FR_ ; FP-BJS to FPR-BJS ; FP-setoid to FPL-setoid ;
       ∨-identityˡ to ∨FR-identityˡ ; ∨-identityʳ to ∨FR-identityʳ ; ⊑-refl to ⊑L₀-refl ; ⊑-reflexive to ⊑R₀-reflexive ;
       sng-free to sng-freeR ; _≤_ to _≤FR_ ; ≈-sym to ≈FR-sym ; _∈_ to _∈R_ ; _∈'_ to _∈R'_ ;
       c1≈c2⇔sameElements to c1≈c2⇔sameElementsR)

    |fL| : |L| → Σ[ l ∈ List (DeltaPoset.Carrier deltaL) ] (IsFreeListL l)
    |fL| = proj₁ $ SemSemilat.f semSemilatL

    |fL|-≈ : ∀ (a b : |L|) → a ≈L b → (|fL| a) ≈FL (|fL| b)
    |fL|-≈ = proj₁ $ proj₂ $ SemSemilat.f semSemilatL

    |fL|-⊥ : |fL| ⊥L ≈FL ⊥FL
    |fL|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilat.f semSemilatL

    |fL|-∨ : ∀ (a b : |L|) → |fL| (a ∨L b) ≈FL ( (|fL| a) ∨FL (|fL| b) ) 
    |fL|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilat.f semSemilatL
 
    |fR| : |R| → Σ[ l ∈ List (DeltaPoset.Carrier deltaR) ] (IsFreeListR l)
    |fR| = proj₁ $ SemSemilat.f semSemilatR

    |fR|-≈ : ∀ (a b : |R|) → a ≈R b → (|fR| a) ≈FR (|fR| b)
    |fR|-≈ = proj₁ $ proj₂ $ SemSemilat.f semSemilatR

    |fR|-⊥ : |fR| ⊥R ≈FR ⊥FR
    |fR|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilat.f semSemilatR

    |fR|-∨ : ∀ (a b : |R|) → |fR| (a ∨R b) ≈FR ( (|fR| a) ∨FR (|fR| b) ) 
    |fR|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilat.f semSemilatR

    gL = SemSemilat.g semSemilatL

    |gL| : Carrier-FPL → |L|
    |gL| = proj₁ $ SemSemilat.g semSemilatL

    |gL|-≈ : (a b : Carrier-FPL) → a ≈FL b → (|gL| a) ≈L (|gL| b) 
    |gL|-≈ = proj₁ $ proj₂ $ SemSemilat.g semSemilatL

    |gL|-⊥ : (|gL| ⊥FL) ≈L ⊥L
    |gL|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilat.g semSemilatL

    |gL|-∨ : ∀ (a b : Carrier-FPL) → |gL| (a ∨FL b) ≈L ( (|gL| a) ∨L (|gL| b) ) 
    |gL|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilat.g semSemilatL

    |gL|-inv-S→FP→S = SemSemilat.inv-S→FP→S semSemilatL

    gR = SemSemilat.g semSemilatR

    |gR| : Carrier-FPR → |R|
    |gR| = proj₁ $ SemSemilat.g semSemilatR

    |gR|-≈ : (a b : Carrier-FPR) → a ≈FR b → (|gR| a) ≈R (|gR| b) 
    |gR|-≈ = proj₁ $ proj₂ $ SemSemilat.g semSemilatR

    |gR|-⊥ : (|gR| ⊥FR) ≈R ⊥R
    |gR|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilat.g semSemilatR

    |gR|-∨ : ∀ (a b : Carrier-FPR) → |gR| (a ∨FR b) ≈R ( (|gR| a) ∨R (|gR| b) ) 
    |gR|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilat.g semSemilatR

    |gR|-inv-S→FP→S = SemSemilat.inv-S→FP→S semSemilatR

{-
    |fR| : |R| → Σ[ l ∈ List (DeltaPoset.Carrier deltaR) ] (IsFreeListR l)
    |fR| = proj₁ $ SemSemilat.f semSemilatR

    |fR|-⊥ : |fR| ⊥R ≈FR ⊥FR
    |fR|-⊥ = proj₁ $ proj₂ $ SemSemilat.f semSemilatR

    |fR|-∨ : ∀ (a b : |R|) → |fR| (a ∨R b) ≈FR ( (|fR| a) ∨FR (|fR| b) ) 
    |fR|-∨ = proj₂ $ proj₂ $ SemSemilat.f semSemilatR
-}

--
    convL : (z : Σ[ l ∈ List |L₀| ] IsFreeListL l) → 
            Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) (proj₁ z) (proj₁ l))
    convL ([] , []-FreeL) = ([] , []-Free) , []
    convL (h ∷ t , ∷-FreeL h t min incomp ft) = 
      ((inj₁ h) ∷ t' , ∷-Free (inj₁ h) t' min' incomp' ft') , (PE.refl ∷ eqt')
      where
        imp1 : ∀ {a : |L₀|} → {b : |P|} → (h <L₀ a) → (b ≡ inj₁ a) → (inj₁ h <P b)
        imp1 {a} {b} h<a b≡injA@PE.refl = ₁∼₁ h<a  

        r : Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) t (proj₁ l))
        r = convL (t , ft)

        t' : List |P|
        t' = proj₁ $ proj₁ r

        ft' : IsFreeList t'
        ft' = proj₂ $ proj₁ r

        eqt' : LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) t t'
        eqt' = proj₂ r

        min' : All (λ z → inj₁ h <P z) t'
        min' = pointwiseRespAll imp1 t t' min eqt'

        ⊑-resp-inj₁ : {a b : |L₀|} → inj₁ a ⊑P inj₁ b → a ⊑L₀ b
        ⊑-resp-inj₁ {a} {b} (₁∼₁ a⊑b) = a⊑b

        p : {a : |P|} → {b : |L₀|} → a ∈≡ t' → (a ≡ inj₁ b) → b ∈≡ t
        p {a} {b} a∈≡t' a≡injb = pointwiseRespAny imp t' t a∈≡t' (LPW.symmetric PE.sym eqt')  
          where
            open import Data.Sum.Properties
            imp : ∀ {x : |P|} → {y : |L₀|} → (a ≡ x) → (inj₁ y ≡ x) → (b ≡ y) 
            imp {x} {y} PE.refl PE.refl = inj₁-injective (PE.sym a≡injb) 

        incomp' : ¬ Any (λ z → inj₁ h ∦P z) t'
        incomp' injh∦t' = anyEliminate t' eliminator injh∦t'
          where
            eliminator : AnyEliminator {ℓQ = l0} |P| ⊥ (inj₁ h ∦P_) t'
            eliminator (inj₁ a') f (inj₂ injh⊑inja') inja'∈≡t' = incomp $ LAny.map (λ a'≡· → PE.subst (h ∦L₀_) a'≡· h∦a') (p inja'∈≡t' PE.refl)    
              where
                h∦a' : h ∦L₀ a'
                h∦a' = inj₂ (⊑-resp-inj₁ injh⊑inja')
            eliminator (inj₁ a') f (inj₁ inja'⊑injh) inja'∈≡t' = incomp $ LAny.map (λ a'≡· → PE.subst (h ∦L₀_) a'≡· h∦a') (p inja'∈≡t' PE.refl)    
              where
                h∦a' : h ∦L₀ a'
                h∦a' = inj₁ (⊑-resp-inj₁ inja'⊑injh)

            eliminator (inj₂ a') f (inj₁ (₁∼₂ ())) inja'∈≡t'
            eliminator (inj₂ a') f (inj₂ ()) inja'∈≡t'

    convR : (z : Σ[ l ∈ List |R₀| ] IsFreeListR l) → 
            Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₂ x)) (proj₁ z) (proj₁ l))
    convR ([] , []-FreeR) = ([] , []-Free) , []
    convR (h ∷ t , ∷-FreeR h t min incomp ft) = 
      ((inj₂ h) ∷ t' , ∷-Free (inj₂ h) t' min' incomp' ft') , (PE.refl ∷ eqt')
      where
        imp1 : ∀ {a : |R₀|} → {b : |P|} → (h <R₀ a) → (b ≡ inj₂ a) → (inj₂ h <P b)
        imp1 {a} {b} h<a b≡injA@PE.refl = ₂∼₂ h<a  

        r : Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₂ x)) t (proj₁ l))
        r = convR (t , ft)

        t' : List |P|
        t' = proj₁ $ proj₁ r

        ft' : IsFreeList t'
        ft' = proj₂ $ proj₁ r

        eqt' : LPW.Pointwise (λ x → λ y → (y ≡ inj₂ x)) t t'
        eqt' = proj₂ r

        min' : All (λ z → inj₂ h <P z) t'
        min' = pointwiseRespAll imp1 t t' min eqt'

        ⊑-resp-inj₂ : {a b : |R₀|} → inj₂ a ⊑P inj₂ b → a ⊑R₀ b
        ⊑-resp-inj₂ {a} {b} (₂∼₂ a⊑b) = a⊑b

        p : {a : |P|} → {b : |R₀|} → a ∈≡ t' → (a ≡ inj₂ b) → b ∈≡ t
        p {a} {b} a∈≡t' a≡injb = pointwiseRespAny imp t' t a∈≡t' (LPW.symmetric PE.sym eqt')  
          where
            open import Data.Sum.Properties
            imp : ∀ {x : |P|} → {y : |R₀|} → (a ≡ x) → (inj₂ y ≡ x) → (b ≡ y) 
            imp {x} {y} PE.refl PE.refl = inj₂-injective (PE.sym a≡injb) 

        incomp' : ¬ Any (λ z → inj₂ h ∦P z) t'
        incomp' injh∦t' = anyEliminate t' eliminator injh∦t'
          where
            eliminator : AnyEliminator {ℓQ = l0} |P| ⊥ (inj₂ h ∦P_) t'
            eliminator (inj₂ a') f (inj₂ injh⊑inja') inja'∈≡t' = incomp $ LAny.map (λ a'≡· → PE.subst (h ∦R₀_) a'≡· h∦a') (p inja'∈≡t' PE.refl)    
              where
                h∦a' : h ∦R₀ a'
                h∦a' = inj₂ (⊑-resp-inj₂ injh⊑inja')
            eliminator (inj₂ a') f (inj₁ inja'⊑injh) inja'∈≡t' = incomp $ LAny.map (λ a'≡· → PE.subst (h ∦R₀_) a'≡· h∦a') (p inja'∈≡t' PE.refl)    
              where
                h∦a' : h ∦R₀ a'
                h∦a' = inj₁ (⊑-resp-inj₂ inja'⊑injh)

            eliminator (inj₁ a') f (inj₁ ()) inja'∈≡t'
            eliminator (inj₁ a') f (inj₂ (₁∼₂ ())) inja'∈≡t'

    convL' : Carrier-FPL → Carrier-FP
    convL' x = proj₁ (convL x)

    convR' : Carrier-FPR → Carrier-FP
    convR' x = proj₁ (convR x)

    convL'-resp-≈FL : {c1 c2 : Carrier-FPL} → (c1 ≈FL c2) → (convL' c1) ≈F (convL' c2) 
    convL'-resp-≈FL {.[] , []-FreeL} {.[] , []-FreeL} [] = ≈F-reflexive {convL' $ [] , []-FreeL} PE.refl
    convL'-resp-≈FL {h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1} {h2 ∷ t2 , ∷-FreeL _ _ min2 incomp2 ft2} (h1~h2 ∷ t1≈t2) = 
      let
        conv-t1≈t2 : (convL' $ t1 , ft1) ≈F (convL' $ t2 , ft2)
        conv-t1≈t2 = convL'-resp-≈FL t1≈t2

        conv-h1-h2 : (inj₁ h1) ~F (inj₁ h2)
        conv-h1-h2 = ₁∼₁ h1~h2
      in
      conv-h1-h2 ∷ conv-t1≈t2

    convR'-resp-≈FR : {c1 c2 : Carrier-FPR} → (c1 ≈FR c2) → (convR' c1) ≈F (convR' c2) 
    convR'-resp-≈FR {.[] , []-FreeL} {.[] , []-FreeL} [] = ≈F-reflexive {convL' $ [] , []-FreeL} PE.refl
    convR'-resp-≈FR {h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1} {h2 ∷ t2 , ∷-FreeL _ _ min2 incomp2 ft2} (h1~h2 ∷ t1≈t2) = 
      let
        conv-t1≈t2 : (convR' $ t1 , ft1) ≈F (convR' $ t2 , ft2)
        conv-t1≈t2 = convR'-resp-≈FR t1≈t2

        conv-h1-h2 : (inj₂ h1) ~F (inj₂ h2)
        conv-h1-h2 = ₂∼₂ h1~h2
      in
      conv-h1-h2 ∷ conv-t1≈t2

    open DeltaPoset.Comparison
    
    convL'-preserves-∨ : (c1 c2 : Carrier-FPL) → ( (convL' (c1 ∨FL c2)) ≈F ( (convL' c1) ∨F (convL' c2) ) )
    convL'-preserves-∨ ([] , []-FreeL) ([] , []-FreeL) = []
    convL'-preserves-∨ ([] , []-FreeL) c2@(h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) = 
      begin 
         convL' (([] , []-FreeL) ∨FL c2) ≈⟨ p ⟩
         convL' c2 ≈⟨ q ⟩ 
         (convL' $ [] , []-FreeL) ∨F (convL' c2)  
       ∎
      where
        open import Relation.Binary.EqReasoning FP-setoid
        p : (convL' (([] , []-FreeL) ∨FL c2)) ≈F (convL' c2)
        p = convL'-resp-≈FL {([] , []-FreeL) ∨FL c2} {c2} $ ∨FL-identityˡ c2

        q : (convL' c2) ≈F ((convL' $ [] , []-FreeL) ∨F (convL' c2))
        q = ≈F-sym {i = convL' c2} {j = (convL' ([] , []-FreeL)) ∨F (convL' c2)} $ ∨F-identityˡ (convL' c2)
    convL'-preserves-∨ c1@(h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) ([] , []-FreeL) = 
       begin 
         convL' (c1 ∨FL ([] , []-FreeL)) ≈⟨ p ⟩
         convL' c1 ≈⟨ q ⟩ 
         (convL' c1) ∨F (convL' $ [] , []-FreeL)   
       ∎
      where
        open import Relation.Binary.EqReasoning FP-setoid
        p : (convL' (c1 ∨FL ([] , []-FreeL))) ≈F (convL' c1)
        p = convL'-resp-≈FL {c1 ∨FL ([] , []-FreeL)} {c1} $ ∨FL-identityʳ c1

        q : (convL' c1) ≈F ((convL' c1) ∨F (convL' $ [] , []-FreeL))
        q = ≈F-sym {i = convL' c1} {j = (convL' ([] , []-FreeL)) ∨F (convL' c1)} $ ∨F-identityʳ (convL' c1)
    convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , ∷-FreeL _ _ min2 incomp2 ft2) with h1 ∦L₀? h2 | (inj₁ h1) ∦P? (inj₁ h2) 
    convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
      convL'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
    convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | r⊑l ¬ih1⊑ih2 (₁∼₁ h2⊑h1) =
      ⊥-elim $ ¬h2⊑h1 h2⊑h1
    convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l≈r ih1~ih2 =
      convL'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
    convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r ih1∥ih2 =
      ⊥-elim $ ih1∥ih2 (inj₁ $ ₁∼₁ h1⊑h2)
    convL'-preserves-∨ (h1 ∷ t1 , ∷-FreeL _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
      ⊥-elim $ ¬ih2⊑ih1 (₁∼₁ h2⊑h1)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | r⊑l ¬ih1⊑ih2 (₁∼₁ _) =
      convL'-preserves-∨ (h1 ∷ t1 , f1) (t2 , ft2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l≈r (₁∼₁ h1~h2) =
      ⊥-elim $ ¬h1⊑h2 (⊑L₀-reflexive h1~h2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l∥r ih1∥ih2 =
      ⊥-elim $ ih1∥ih2 (inj₂ $ ₁∼₁ h2⊑h1)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
      ⊥-elim $ ¬ih2⊑ih1 (₁∼₁ $ ⊑L₀-reflexive (≈L₀-sym h1~h2))
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l≈r h1~h2 | r⊑l ¬ih1⊑ih2 (₁∼₁ _) =
      ⊥-elim $ ¬ih1⊑ih2 (₁∼₁ $ ⊑L₀-reflexive h1~h2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l≈r (₁∼₁ _) =
      convL'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l∥r ih1∥ih2 =
      ⊥-elim $ ih1∥ih2 (inj₁ (₁∼₁ $ ⊑L₀-reflexive h1~h2))
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l⊑r (₁∼₁ h1⊑h2) ¬ih2⊑ih1 =
      ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | r⊑l ¬ih1⊑ih2 (₁∼₁ h2⊑h1) =
      ⊥-elim $ h1∥h2 (inj₂ h2⊑h1)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l≈r (₁∼₁ h1≈h2) =
      ⊥-elim $ h1∥h2 (inj₁ $ ⊑L₀-reflexive h1≈h2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 with compareL₀ h1 h2 | compareP (inj₁ h1) (inj₁ h2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri< (₁∼₁ _) _ _ =
      (₁∼₁ $ ≈L₀-refl) ∷ convL'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri≈ _ (₁∼₁ h1~h2) _ =
      ⊥-elim $ irreflL₀ h1~h2 h1<h2
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri> _ _ (₁∼₁ h2<h1) =
      ⊥-elim $ irreflL₀ ≈L₀-refl (<L₀-trans h1<h2 h2<h1)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri< (₁∼₁ h1<h2) _ _ =
      ⊥-elim $ h1∥h2 (inj₁ $ ⊑L₀-reflexive h1~h2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri≈ _ (₁∼₁ _) _ =
      ⊥-elim $ h1∥h2 (inj₁ $ ⊑L₀-reflexive h1~h2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri> _ _ (₁∼₁ h2<h1) =
      ⊥-elim $ h1∥h2 (inj₁ $ ⊑L₀-reflexive h1~h2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri< (₁∼₁ h1<h2) _ _ =
      ⊥-elim $ irreflL₀ ≈L₀-refl (<L₀-trans h1<h2 h2<h1)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri≈ _ (₁∼₁ h1~h2) _ =
      ⊥-elim $ h1∥h2 (inj₁ $ ⊑L₀-reflexive h1~h2)
    convL'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeL _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeL _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri> _ _ (₁∼₁ _) =
      (₁∼₁ $ ≈L₀-refl) ∷ convL'-preserves-∨ (h1 ∷ t1 , f1) (t2 , ft2)

    convR'-preserves-∨ : (c1 c2 : Carrier-FPR) → ( (convR' (c1 ∨FR c2)) ≈F ( (convR' c1) ∨F (convR' c2) ) )  
    convR'-preserves-∨ ([] , []-FreeR) ([] , []-FreeR) = []
    convR'-preserves-∨ ([] , []-FreeR) c2@(h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) = 
      begin 
         convR' (([] , []-FreeR) ∨FR c2) ≈⟨ p ⟩
         convR' c2 ≈⟨ q ⟩ 
         (convR' $ [] , []-FreeR) ∨F (convR' c2)  
       ∎
      where
        open import Relation.Binary.EqReasoning FP-setoid
        p : (convR' (([] , []-FreeR) ∨FR c2)) ≈F (convR' c2)
        p = convR'-resp-≈FR {([] , []-FreeR) ∨FR c2} {c2} $ ∨FR-identityˡ c2

        q : (convR' c2) ≈F ((convR' $ [] , []-FreeR) ∨F (convR' c2))
        q = ≈F-sym {i = convR' c2} {j = (convR' ([] , []-FreeR)) ∨F (convR' c2)} $ ∨F-identityˡ (convR' c2)
    convR'-preserves-∨ c1@(h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) ([] , []-FreeR) = 
       begin 
         convR' (c1 ∨FR ([] , []-FreeR)) ≈⟨ p ⟩
         convR' c1 ≈⟨ q ⟩ 
         (convR' c1) ∨F (convR' $ [] , []-FreeR)   
       ∎
      where
        open import Relation.Binary.EqReasoning FP-setoid
        p : (convR' (c1 ∨FR ([] , []-FreeR))) ≈F (convR' c1)
        p = convR'-resp-≈FR {c1 ∨FR ([] , []-FreeR)} {c1} $ ∨FR-identityʳ c1

        q : (convR' c1) ≈F ((convR' c1) ∨F (convR' $ [] , []-FreeR))
        q = ≈F-sym {i = convR' c1} {j = (convR' ([] , []-FreeR)) ∨F (convR' c1)} $ ∨F-identityʳ (convR' c1)
    convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , ∷-FreeR _ _ min2 incomp2 ft2) with h1 ∦R₀? h2 | (inj₂ h1) ∦P? (inj₂ h2) 
    convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
      convR'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
    convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | r⊑l ¬ih1⊑ih2 (₂∼₂ h2⊑h1) =
      ⊥-elim $ ¬h2⊑h1 h2⊑h1
    convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l≈r ih1~ih2 =
      convR'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
    convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l⊑r h1⊑h2 ¬h2⊑h1 | l∥r ih1∥ih2 =
      ⊥-elim $ ih1∥ih2 (inj₁ $ ₂∼₂ h1⊑h2)
    convR'-preserves-∨ (h1 ∷ t1 , ∷-FreeR _ _ min1 incomp1 ft1) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
      ⊥-elim $ ¬ih2⊑ih1 (₂∼₂ h2⊑h1)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | r⊑l ¬ih1⊑ih2 (₂∼₂ _) =
      convR'-preserves-∨ (h1 ∷ t1 , f1) (t2 , ft2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l≈r (₂∼₂ h1~h2) =
      ⊥-elim $ ¬h1⊑h2 (⊑R₀-reflexive h1~h2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | r⊑l ¬h1⊑h2 h2⊑h1 | l∥r ih1∥ih2 =
      ⊥-elim $ ih1∥ih2 (inj₂ $ ₂∼₂ h2⊑h1)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l⊑r ih1⊑ih2 ¬ih2⊑ih1 =
      ⊥-elim $ ¬ih2⊑ih1 (₂∼₂ $ ⊑R₀-reflexive (≈R₀-sym h1~h2))
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l≈r h1~h2 | r⊑l ¬ih1⊑ih2 (₂∼₂ _) =
      ⊥-elim $ ¬ih1⊑ih2 (₂∼₂ $ ⊑R₀-reflexive h1~h2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l≈r (₂∼₂ _) =
      convR'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l≈r h1~h2 | l∥r ih1∥ih2 =
      ⊥-elim $ ih1∥ih2 (inj₁ (₂∼₂ $ ⊑R₀-reflexive h1~h2))
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l⊑r (₂∼₂ h1⊑h2) ¬ih2⊑ih1 =
      ⊥-elim $ h1∥h2 (inj₁ h1⊑h2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | r⊑l ¬ih1⊑ih2 (₂∼₂ h2⊑h1) =
      ⊥-elim $ h1∥h2 (inj₂ h2⊑h1)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l≈r (₂∼₂ h1≈h2) =
      ⊥-elim $ h1∥h2 (inj₁ $ ⊑R₀-reflexive h1≈h2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 with compareR₀ h1 h2 | compareP (inj₂ h1) (inj₂ h2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri< (₂∼₂ _) _ _ =
      (₂∼₂ $ ≈R₀-refl) ∷ convR'-preserves-∨ (t1 , ft1) (h2 ∷ t2 , f2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri≈ _ (₂∼₂ h1~h2) _ =
      ⊥-elim $ irreflR₀ h1~h2 h1<h2
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri< h1<h2 _ _ | tri> _ _ (₂∼₂ h2<h1) =
      ⊥-elim $ irreflR₀ ≈R₀-refl (<R₀-trans h1<h2 h2<h1)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri< (₂∼₂ h1<h2) _ _ =
      ⊥-elim $ h1∥h2 (inj₁ $ ⊑R₀-reflexive h1~h2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri≈ _ (₂∼₂ _) _ =
      ⊥-elim $ h1∥h2 (inj₁ $ ⊑R₀-reflexive h1~h2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri≈ _ h1~h2 _ | tri> _ _ (₂∼₂ h2<h1) =
      ⊥-elim $ h1∥h2 (inj₁ $ ⊑R₀-reflexive h1~h2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri< (₂∼₂ h1<h2) _ _ =
      ⊥-elim $ irreflR₀ ≈R₀-refl (<R₀-trans h1<h2 h2<h1)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri≈ _ (₂∼₂ h1~h2) _ =
      ⊥-elim $ h1∥h2 (inj₁ $ ⊑R₀-reflexive h1~h2)
    convR'-preserves-∨ (h1 ∷ t1 , f1@(∷-FreeR _ _ min1 incomp1 ft1)) (h2 ∷ t2 , f2@(∷-FreeR _ _ min2 incomp2 ft2)) | l∥r h1∥h2 | l∥r ih1∥ih2 | tri> _ _ h2<h1 | tri> _ _ (₂∼₂ _) =
      (₂∼₂ $ ≈R₀-refl) ∷ convR'-preserves-∨ (h1 ∷ t1 , f1) (t2 , ft2)

    pL : proj₁ (|fL| ⊥L) ≡ []
    pL = pointwise-[]ʳ |fL|-⊥ 

    pL' : (|fL| ⊥L) ≡ ([] , []-FreeL)
    pL' with |fL| ⊥L | pL
    pL' | ([] , []-FreeR) | PE.refl  = PE.refl
    pL' | (h ∷ t , ∷-FreeR _ _ _ _ _) | ()

    pR : proj₁ (|fR| ⊥R) ≡ []
    pR = pointwise-[]ʳ |fR|-⊥ 

    pR' : (|fR| ⊥R) ≡ ([] , []-FreeR)
    pR' with |fR| ⊥R | pR
    pR' | ([] , []-FreeR) | PE.refl  = PE.refl
    pR' | (h ∷ t , ∷-FreeR _ _ _ _ _) | ()

    convL-⊥ : proj₁ (convL $ |fL| ⊥L) ≡ ⊥F
    convL-⊥ rewrite pL' = PE.refl

    convR-⊥ : proj₁ (convR $ |fR| ⊥R) ≡ ⊥F
    convR-⊥ rewrite pR' = PE.refl

    P-|f| : (a : Carrier') → (x : |P|) → Set
    P-|f| (aL , aR) x = (Σ[ y ∈ |L₀| ] (x ≈P inj₁ y) × (y ∈L |fL| aL)) ⊎ (Σ[ y ∈ |R₀| ] (x ≈P inj₂ y) × (y ∈R |fR| aR))

    |f|-aux : (a : Carrier') → Σ[ c ∈ Carrier-FP ] ∀ (x : |P|) → x ∈P c ⇔ P-|f| a x 
    |f|-aux (aL , aR) =
      let
        res , _ = concat-FP (resL-list , resL-free) (resR-list , resR-free) min incomp
      in
        res , res-prop⇔
      where
        open import FreeSemilattice.Core P using (concat-FP)
        
        factoredL : Σ[ l ∈ List |L₀| ] (IsFreeListL l)
        factoredL = |fL| aL

        factoredR : Σ[ l ∈ List |R₀| ] (IsFreeListR l)
        factoredR = |fR| aR

        resL : Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) (proj₁ factoredL) (proj₁ l))
        resL = convL factoredL

        resR : Σ[ l ∈ Carrier-FP ] (LPW.Pointwise (λ x → λ y → (y ≡ inj₂ x)) (proj₁ factoredR) (proj₁ l))
        resR = convR factoredR

        resL-list : List |P|
        resL-list = proj₁ $ proj₁ resL

        resR-list : List |P|
        resR-list = proj₁ $ proj₁ resR

        resL-free : IsFreeList resL-list
        resL-free = proj₂ $ proj₁ resL

        resR-free : IsFreeList resR-list
        resR-free = proj₂ $ proj₁ resR

        resL-eq : (LPW.Pointwise (λ x → λ y → (y ≡ inj₁ x)) (proj₁ factoredL) resL-list)
        resL-eq = proj₂ resL

        resR-eq : (LPW.Pointwise (λ x → λ y → (y ≡ inj₂ x)) (proj₁ factoredR) resR-list)
        resR-eq = proj₂ resR

        min : All (λ x → All (x <P_) resR-list) resL-list
        min = pointwiseRespAll imp (proj₁ factoredL) resL-list U-L resL-eq
          where
            open import Relation.Unary using (Universal ; U)
            open import Relation.Unary.Properties
            open import Data.List.All.Properties

            U-L : All U (proj₁ factoredL)
            U-L = All-universal U-Universal (proj₁ factoredL)

            U-R : All U (proj₁ factoredR)
            U-R = All-universal U-Universal (proj₁ factoredR)

            imp : ∀ {a b} → U a → (b ≡ inj₁ a) → All (b <P_) resR-list
            imp {a} {b} _ b≡inj₁a = pointwiseRespAll imp' (proj₁ factoredR) resR-list U-R resR-eq
              where 
                imp' : ∀ {x y} → U x → (y ≡ inj₂ x) → b <P y
                imp' {x} {y} _ y≡inj₂x rewrite b≡inj₁a | y≡inj₂x = ₁∼₂ tt 
   
        incomp : All (λ x → All (x ∥P_) resR-list) resL-list
        incomp = pointwiseRespAll imp (proj₁ factoredL) resL-list U-L resL-eq
          where
            open import Relation.Unary using (Universal ; U)
            open import Relation.Unary.Properties
            open import Data.List.All.Properties

            U-L : All U (proj₁ factoredL)
            U-L = All-universal U-Universal (proj₁ factoredL)

            U-R : All U (proj₁ factoredR)
            U-R = All-universal U-Universal (proj₁ factoredR)        

            imp : ∀ {a b} → U a → (b ≡ inj₁ a) → All (b ∥P_) resR-list
            imp {a} {b} _ PE.refl = pointwiseRespAll imp' (proj₁ factoredR) resR-list U-R resR-eq
              where 
                imp' : ∀ {x y} → U x → (y ≡ inj₂ x) → b ∥P y
                imp' {x} {.(inj₂ x)} _ PE.refl (inj₁ (₁∼₂ ()))
                imp' {x} {.(inj₂ x)} _ PE.refl (inj₂ ()) 

        res : Carrier-FP
        res = proj₁ $ concat-FP (resL-list , resL-free) (resR-list , resR-free) min incomp
    
        concat-property : (proj₁ res) ≡ (resL-list) ++ (resR-list)
        concat-property = proj₂ $ concat-FP (resL-list , resL-free) (resR-list , resR-free) min incomp
        
        res-prop← : ∀ (x : |P|) → (Σ[ y ∈ |L₀| ] (x ≈P inj₁ y) × (y ∈L |fL| aL)) ⊎ (Σ[ y ∈ |R₀| ] (x ≈P inj₂ y) × (y ∈R |fR| aR)) → 
                        (x ∈P res)
        res-prop← x (inj₁ (y , x-≈P-inj₁y , y-∈L~fLaL)) rewrite concat-property = ∈-++⁺ˡ ≈P-setoid p''
          where
            open import Data.List.Membership.Setoid.Properties
            imp : ∀ {a : |P|} → {b : |L₀|} → (y ≈L₀ b) → (a ≡ inj₁ b) → (a ≈P inj₁ y)
            imp {a} {b} y-≈L₀-b a-≡-inj₁b = DeltaPoset.Eq.trans P a-≈P-inj₁b (₁∼₁ (≈L₀-sym y-≈L₀-b))  
              where
                open Setoid ≈P-setoid

                a-≈P-inj₁b : a ≈P inj₁ b
                a-≈P-inj₁b = ≈P-reflexive a-≡-inj₁b

            -- step 1 : since y ∈L fLaL, we have inj₁ y ∈P convL fLaL
            p : Any (λ · → · ≈P inj₁ y) resL-list
            p = pointwiseRespAny imp (proj₁ $ |fL| aL) resL-list y-∈L~fLaL resL-eq 

            p' : inj₁ y ∈P proj₁ resL
            p' = LAny.map (λ ·-≈P-inj₁y → DeltaPoset.Eq.sym P ·-≈P-inj₁y) p

            p'' : x ∈P proj₁ resL
            p'' = LAny.map (λ inj₁y-≈P-· → DeltaPoset.Eq.trans P x-≈P-inj₁y inj₁y-≈P-·) p'

        res-prop← x (inj₂ (y , x-≈P-inj₂y , y-∈R~fRaR)) rewrite concat-property = ∈-++⁺ʳ ≈P-setoid resL-list p''
          where
            open import Data.List.Membership.Setoid.Properties
            imp : ∀ {a : |P|} → {b : |R₀|} → (y ≈R₀ b) → (a ≡ inj₂ b) → (a ≈P inj₂ y)
            imp {a} {b} y-≈R₀-b a-≡-inj₂b = DeltaPoset.Eq.trans P a-≈P-inj₂b (₂∼₂ (≈R₀-sym y-≈R₀-b))  
              where
                open Setoid ≈P-setoid

                a-≈P-inj₂b : a ≈P inj₂ b
                a-≈P-inj₂b = ≈P-reflexive a-≡-inj₂b

            p : Any (λ · → · ≈P inj₂ y) resR-list
            p = pointwiseRespAny imp (proj₁ $ |fR| aR) resR-list y-∈R~fRaR resR-eq 

            p' : inj₂ y ∈P proj₁ resR
            p' = LAny.map (λ ·-≈P-inj₁y → DeltaPoset.Eq.sym P ·-≈P-inj₁y) p

            p'' : x ∈P proj₁ resR
            p'' = LAny.map (λ inj₂y-≈P-· → DeltaPoset.Eq.trans P x-≈P-inj₂y inj₂y-≈P-·) p'


        res-prop→ : ∀ (x : |P|) → x ∈P res →  
                       (Σ[ y ∈ |L₀| ] (x ≈P inj₁ y) × (y ∈L |fL| aL)) ⊎
                       (Σ[ y ∈ |R₀| ] (x ≈P inj₂ y) × (y ∈R |fR| aR))
        res-prop→ x x∈res with x∈resL⊎resR
          where
            open import Data.List.Membership.Setoid.Properties
            x∈resL⊎resR : x ∈P (proj₁ resL) ⊎ x ∈P (proj₁ resR)
            x∈resL⊎resR = ∈-++⁻ ≈P-setoid resL-list (PE.subst (λ z → x ∈P' z) concat-property x∈res)
        res-prop→ x x∈res | (inj₁ x∈resL) = inj₁ $ anyEliminate (proj₁ $ |fL| aL) elim p
          where
            imp : ∀ {a : |P|} → {b : |L₀|} → (x ≈P a) → (a ≡ inj₁ b) → (x ≈P inj₁ b)
            imp {a} {b} x≈a a≡inj₁b = PE.subst (λ · → x ≈P ·) a≡inj₁b x≈a 

            p : Any (λ · → x ≈P inj₁ ·) (proj₁ $ |fL| aL)
            p = pointwiseRespAny⃖ imp (proj₁ $ |fL| aL) resL-list x∈resL resL-eq

            elim : AnyEliminator {ℓQ = l0} |L₀| (Σ[ y ∈ |L₀| ] (x ≈P inj₁ y) × (y ∈L |fL| aL)) (λ · → x ≈P inj₁ ·) (proj₁ $ |fL| aL) 
            elim a f x≈Pa a∈≡fLaL = (a , x≈Pa , LAny.map (λ a∈≡· → ≈L₀-reflexive a∈≡·) a∈≡fLaL)
        res-prop→ x x∈res | (inj₂ x∈resR) = inj₂ $ anyEliminate (proj₁ $ |fR| aR) elim p
          where
            imp : ∀ {a : |P|} → {b : |R₀|} → (x ≈P a) → (a ≡ inj₂ b) → (x ≈P inj₂ b)
            imp {a} {b} x≈a a≡inj₂b = PE.subst (λ · → x ≈P ·) a≡inj₂b x≈a 

            p : Any (λ · → x ≈P inj₂ ·) (proj₁ $ |fR| aR)
            p = pointwiseRespAny⃖ imp (proj₁ $ |fR| aR) resR-list x∈resR resR-eq

            elim : AnyEliminator {ℓQ = l0} |R₀| (Σ[ y ∈ |R₀| ] (x ≈P inj₂ y) × (y ∈R |fR| aR)) (λ · → x ≈P inj₂ ·) (proj₁ $ |fR| aR) 
            elim a f x≈Pa a∈≡fRaR = (a , x≈Pa , LAny.map (λ a∈≡· → ≈R₀-reflexive a∈≡·) a∈≡fRaR)

        res-prop⇔ : (x : |P|) → (x ∈P res) ⇔ P-|f| (aL , aR) x
        res-prop⇔ x = equivalence (res-prop→ x) (res-prop← x)

    |f| : Carrier' → Carrier-FP
    |f| c = proj₁ $ |f|-aux c
    
    |f|-prop : (c : Carrier') → (x : |P|) → (x ∈P (|f| c)) ⇔ (P-|f| c x)
    |f|-prop c = proj₂ $ |f|-aux c
    
{- 
    module _ where
      open import Data.List.Membership.Setoid ≈P-setoid renaming (_∈_ to _∈P_) 
      open import Data.List.Membership.Setoid ≈L₀-setoid renaming (_∈_ to _∈L_)
      open import Data.List.Membership.Setoid ≈R₀-setoid renaming (_∈_ to _∈R_)

      |f|-prop : (c : Carrier') → (x : |P|) → (x ∈P (proj₁ $ |f| c)) → 
                 (Σ[ y ∈ |L₀| ] (x ≡ inj₁ y) × (y ∈L (proj₁ $ |fL| (proj₁ c)))) ⊎ (Σ[ y ∈ |R₀| ] (x ≡ inj₂ y) × (y ∈R (proj₁ $ |fR| (proj₂ c))))
      |f|-prop (cL , cR) (inj₁ x') x∈fc = {!!}
      |f|-prop (cL , cR) (inj₂ x') x∈fc = {!!}
-}
 

    {-
    |f|-≈ : (a b : Carrier') → (a ≈' b) → (|f| a) ≈F (|f| b)  
    |f|-≈ a@(aL , aR) b@(bL , bR) (aL≈bL , aR≈bR) = 
      begin
        (|f| a) ≡⟨ PE.refl ⟩
        (convL' $ |fL| aL) ∨F (convR' $ |fR| $ aR) ≈⟨ ∨F-congˡ {convL' $ |fL| aL} {convL' $ |fL| bL} (convR' $ |fR| aR) $ convL'-resp-≈FL (|fL|-≈ aL bL aL≈bL) ⟩
        (convL' $ |fL| bL) ∨F (convR' $ |fR| $ aR) ≈⟨ ∨F-congʳ {convR' $ |fR| aR} {convR' $ |fR| bR} (convL' $ |fL| bL) $ convR'-resp-≈FR (|fR|-≈ aR bR aR≈bR) ⟩
        (convL' $ |fL| bL) ∨F (convR' $ |fR| $ bR) ≡⟨ PE.refl ⟩
        (|f| b)
       ∎
      where
        open import Relation.Binary.EqReasoning FP-setoid

    |f|-⊥ : |f| (⊥L , ⊥R) ≈F ⊥F
    |f|-⊥ = ≈F-reflexive p
      where
        p : |f| (⊥L , ⊥R) ≡ ⊥F 
        p rewrite pL' | pR' = PE.refl
    
    |f|-∨ : (a b : Carrier') → (|f| $ a ∨' b) ≈F ((|f| a) ∨F (|f| b))
    |f|-∨ a@(aL , aR) b@(bL , bR) =
      begin
        |f| (a ∨' b) ≡⟨ PE.cong (λ · → |f| $ ·) p ⟩
        |f| (aL ∨L bL , aR ∨R bR) ≡⟨ PE.refl ⟩ 
        ( (proj₁ $ convL $ |fL| $ aL ∨L bL) ∨F (proj₁ $ convR $ |fR| $ aR ∨R bR) ) ≈⟨ ∨F-congˡ {proj₁ $ convL $ |fL| $ aL ∨L bL} {convL' $ (|fL| aL) ∨FL (|fL| bL)} (proj₁ $ convR $ |fR| $ aR ∨R bR) rL ⟩
        ( (convL' $ (|fL| aL) ∨FL (|fL| bL)) ∨F (proj₁ $ convR $ |fR| $ aR ∨R bR) ) ≈⟨ ∨F-congˡ {convL' $ (|fL| aL) ∨FL (|fL| bL)} {(convL' $ |fL| aL) ∨F (convL' $ |fL| bL)} (proj₁ $ convR $ |fR| $ aR ∨R bR) qL ⟩
        ( ((convL' $ |fL| aL) ∨F (convL' $ |fL| bL)) ∨F (proj₁ $ convR $ |fR| $ aR ∨R bR) ) ≈⟨ ∨F-congʳ {proj₁ $ convR $ |fR| $ aR ∨R bR} {proj₁ $ convR $ (|fR| aR) ∨FR (|fR| bR)} ((convL' $ |fL| aL) ∨F (convL' $ |fL| bL)) rR ⟩
        ( ((convL' $ |fL| aL) ∨F (convL' $ |fL| bL)) ∨F (proj₁ $ convR $ (|fR| aR) ∨FR (|fR| bR)) ) ≈⟨ ∨F-congʳ {proj₁ $ convR $ (|fR| aR) ∨FR (|fR| bR)} {(convR' $ |fR| aR) ∨F (convR' $ |fR| bR)} ((convL' $ |fL| aL) ∨F (convL' $ |fL| bL)) qR ⟩
        ( (caL ∨F cbL) ∨F (caR ∨F cbR) ) ≈⟨  ∨F-assoc caL cbL (caR ∨F cbR) ⟩
        ( caL ∨F (cbL ∨F (caR ∨F cbR)) ) ≈⟨ ∨F-congʳ {cbL ∨F (caR ∨F cbR)} {(cbL ∨F caR) ∨F cbR} caL $ ≈F-sym {(cbL ∨F caR) ∨F cbR} {cbL ∨F (caR ∨F cbR)} (∨F-assoc cbL caR cbR) ⟩
        ( caL ∨F ((cbL ∨F caR) ∨F cbR) ) ≈⟨ ∨F-congʳ {(cbL ∨F caR) ∨F cbR} {(caR ∨F cbL) ∨F cbR} caL $ ∨F-congˡ {cbL ∨F caR} {caR ∨F cbL} cbR $ ∨F-comm cbL caR ⟩ 
        ( caL ∨F ((caR ∨F cbL) ∨F cbR) ) ≈⟨ ≈F-sym {(caL ∨F (caR ∨F cbL)) ∨F cbR} {caL ∨F ((caR ∨F cbL) ∨F cbR)} $ ∨F-assoc caL (caR ∨F cbL) cbR ⟩ 
        ( (caL ∨F (caR ∨F cbL)) ∨F cbR ) ≈⟨ ∨F-congˡ {caL ∨F (caR ∨F cbL)} {(caL ∨F caR) ∨F cbL} cbR $ ≈F-sym {(caL ∨F caR) ∨F cbL} {caL ∨F (caR ∨F cbL)} (∨F-assoc caL caR cbL) ⟩
        ( ((caL ∨F caR) ∨F cbL) ∨F cbR ) ≈⟨ ∨F-assoc (caL ∨F caR) cbL cbR ⟩ 
        ( (caL ∨F caR) ∨F (cbL ∨F cbR) ) ≡⟨ PE.refl ⟩ 
        ((|f| a) ∨F (|f| b))
       ∎
      where
        open import Relation.Binary.EqReasoning FP-setoid
        p : (aL , aR) ∨' (bL , bR) ≡ (aL ∨L bL , aR ∨R bR)
        p = PE.refl

        rL : (convL' $ |fL| $ aL ∨L bL) ≈F (convL' $ (|fL| aL) ∨FL (|fL| bL))
        rL = convL'-resp-≈FL (|fL|-∨ aL bL)

        qL : (convL' $ (|fL| aL) ∨FL (|fL| bL)) ≈F ( (convL' $ |fL| aL) ∨F (convL' $ |fL| bL) )
        qL = convL'-preserves-∨ (|fL| aL) (|fL| bL)

        rR : (convR' $ |fR| $ aR ∨R bR) ≈F (convR' $ (|fR| aR) ∨FR (|fR| bR))
        rR = convR'-resp-≈FR (|fR|-∨ aR bR)

        qR : (convR' $ (|fR| aR) ∨FR (|fR| bR)) ≈F ( (convR' $ |fR| aR) ∨F (convR' $ |fR| bR) )
        qR = convR'-preserves-∨ (|fR| aR) (|fR| bR)

        caL = convL' (|fL| aL)
        caR = convR' (|fR| aR)
        cbL = convL' (|fL| bL)
        cbR = convR' (|fR| bR)
    -}

    decompose : (c : Carrier-FP) → 
              Σ[ l ∈ Carrier-FPL ] Σ[ r ∈ Carrier-FPR ] Σ[ tl ∈ Carrier-FP ] Σ[ tr ∈ Carrier-FP ]
              LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ l) (proj₁ tl) ×
              LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ r) (proj₁ tr) ×
              (proj₁ c) ≡ (proj₁ tl) ++ (proj₁ tr)
    decompose ([] , []-Free) = 
      ([] , []-FreeL) , 
      ([] , []-FreeR) , 
      ([] , []-Free) , 
      ([] , []-Free) , 
      [] , 
      [] ,
      ++-identityˡ []
      where
        open import Data.List.Properties
    decompose ((inj₁ h') ∷ t , ∷-Free .(inj₁ h') .t min incomp ft) =
       (h' ∷ (proj₁ restL) , ∷-FreeL h' (proj₁ restL) minL incompL (proj₂ restL)) , 
       restR , 
       (inj₁ h' ∷ (proj₁ restTL) , ∷-Free (inj₁ h') (proj₁ restTL) minTL incompTL (proj₂ restTL))  , 
       restTR , 
       PE.refl ∷ rest-eql , 
       rest-eqr , 
       PE.cong (λ · → inj₁ h' ∷ ·) rest-concat
      where
        rest : Σ[ l ∈ Carrier-FPL ] Σ[ r ∈ Carrier-FPR ] Σ[ tl ∈ Carrier-FP ] Σ[ tr ∈ Carrier-FP ]
               LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ l) (proj₁ tl) ×
               LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ r) (proj₁ tr) ×
               t ≡ (proj₁ tl) ++ (proj₁ tr)

        rest = decompose (t , ft)

        restL : Carrier-FPL
        restL = let l , _ , _ , _ , _ , _ , _ = rest in l

        restR : Carrier-FPR
        restR = let _ , r , _ , _ , _ , _ , _ = rest in r

        restTL : Carrier-FP
        restTL = let _ , _ , tl , _ , _ , _ , _ = rest in tl

        restTR : Carrier-FP
        restTR = let _ , _ , _ , tr , _ , _ , _ = rest in tr

        rest-eql : LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ restL) (proj₁ restTL)
        rest-eql = let _ , _ , _ , _ , eql , _ , _ = rest in eql

        rest-eqr : LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ restR) (proj₁ restTR)
        rest-eqr = let _ , _ , _ , _ , _ , eqr , _ = rest in eqr

        rest-concat : t ≡ (proj₁ restTL) ++ (proj₁ restTR)
        rest-concat = let _ , _ , _ , _ , _ , _ , conc = rest in conc

        minL : All (h' <L₀_) (proj₁ restL)
        minL =
          pointwiseRespAll⃖ imp (proj₁ restL) (proj₁ restTL) p' rest-eql
          where
            open import Data.List.All.Properties
            
            p : All (inj₁ h' <P_) ((proj₁ restTL) ++ (proj₁ restTR))
            p rewrite PE.sym rest-concat = min 
            
            p' : All (inj₁ h' <P_) (proj₁ restTL)
            p' = ++⁻ˡ (proj₁ restTL) p
            
            imp : {a : |L₀|} → {b : |P|} → (inj₁ h' <P b) → (b ≡ inj₁ a) → (h' <L₀ a)
            imp {a} {b} (₁∼₁ h'<a) b≡inj₁a@PE.refl = h'<a
 
        minTL : All (inj₁ h' <P_) (proj₁ restTL)
        minTL = ++⁻ˡ (proj₁ restTL) p
          where
            open import Data.List.All.Properties
            
            p : All (inj₁ h' <P_) ((proj₁ restTL) ++ (proj₁ restTR))
            p rewrite PE.sym rest-concat = min     
        
        incompL : ¬ Any (h' ∦L₀_) (proj₁ restL)
        incompL h'∦restL = ⊥-elim $ incomp p'
          where
            open import Data.List.Any.Properties

            imp : {a : |L₀|} → {b : |P|} → h' ∦L₀ a → b ≡ inj₁ a → (inj₁ h') ∦P b
            imp {a} {b} (inj₁ h'⊑a) b≡inj₁a@PE.refl = inj₁ (₁∼₁ h'⊑a)
            imp {a} {b} (inj₂ a⊑h') b≡inj₁a@PE.refl = inj₂ (₁∼₁ a⊑h')

            p : Any (inj₁ h' ∦P_) (proj₁ restTL)
            p = pointwiseRespAny imp (proj₁ restL) (proj₁ restTL) h'∦restL rest-eql

            p' : Any (inj₁ h' ∦P_) t
            p' = PE.subst (λ · → Any (inj₁ h' ∦P_) ·) (PE.sym rest-concat) (++⁺ˡ p) 
            
        incompTL : ¬ Any (inj₁ h' ∦P_) (proj₁ restTL)
        incompTL inj₁h'∦restTL = ⊥-elim $ incomp p'
          where
            open import Data.List.Any.Properties

            p' : Any (inj₁ h' ∦P_) t
            p' = PE.subst (λ · → Any (inj₁ h' ∦P_) ·) (PE.sym rest-concat) (++⁺ˡ inj₁h'∦restTL) 

    decompose ((inj₂ h') ∷ t , ∷-Free .(inj₂ h') .t min incomp ft) =
       restL ,
       (h' ∷ (proj₁ restR) , ∷-FreeR h' (proj₁ restR) minR incompR (proj₂ restR)) , 
       restTL ,
       (inj₂ h' ∷ (proj₁ restTR) , ∷-Free (inj₂ h') (proj₁ restTR) minTR incompTR (proj₂ restTR))  , 
       rest-eql ,
       PE.refl ∷ rest-eqr ,
       (begin
          inj₂ h' ∷ t ≡⟨ ++-identityˡ (inj₂ h' ∷ t) ⟩
          [] ++ (inj₂ h' ∷ t) ≡⟨ PE.cong (λ · → · ++ (inj₂ h' ∷ t)) $ PE.sym restTL-empty ⟩
          (proj₁ restTL) ++ (inj₂ h' ∷ t) ≡⟨ PE.cong (λ · → (proj₁ restTL) ++ (inj₂ h' ∷ ·)) rest-concat ⟩
          (proj₁ restTL) ++ (inj₂ h' ∷ (proj₁ restTL) ++ (proj₁ restTR)) ≡⟨ PE.cong (λ · → (proj₁ restTL) ++ (inj₂ h' ∷ (· ++ (proj₁ restTR)))) $ restTL-empty ⟩ 
          (proj₁ restTL) ++ (inj₂ h' ∷ [] ++ (proj₁ restTR)) ≡⟨ PE.cong (λ · → (proj₁ restTL) ++ (inj₂ h' ∷ ·)) $ ++-identityˡ (proj₁ restTR) ⟩ 
          (proj₁ restTL) ++ (inj₂ h' ∷ (proj₁ restTR)) 
         ∎) 
      where
        open PE.≡-Reasoning
        rest : Σ[ l ∈ Carrier-FPL ] Σ[ r ∈ Carrier-FPR ] Σ[ tl ∈ Carrier-FP ] Σ[ tr ∈ Carrier-FP ]
               LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ l) (proj₁ tl) ×
               LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ r) (proj₁ tr) ×
               t ≡ (proj₁ tl) ++ (proj₁ tr)

        rest = decompose (t , ft)

        restL : Carrier-FPL
        restL = let l , _ , _ , _ , _ , _ , _ = rest in l

        restR : Carrier-FPR
        restR = let _ , r , _ , _ , _ , _ , _ = rest in r

        restTL : Carrier-FP
        restTL = let _ , _ , tl , _ , _ , _ , _ = rest in tl

        restTR : Carrier-FP
        restTR = let _ , _ , _ , tr , _ , _ , _ = rest in tr

        rest-eql : LPW.Pointwise (λ x → λ y → y ≡ inj₁ x) (proj₁ restL) (proj₁ restTL)
        rest-eql = let _ , _ , _ , _ , eql , _ , _ = rest in eql

        rest-eqr : LPW.Pointwise (λ x → λ y → y ≡ inj₂ x) (proj₁ restR) (proj₁ restTR)
        rest-eqr = let _ , _ , _ , _ , _ , eqr , _ = rest in eqr

        rest-concat : t ≡ (proj₁ restTL) ++ (proj₁ restTR)
        rest-concat = let _ , _ , _ , _ , _ , _ , conc = rest in conc

        minTL : All (inj₂ h' <P_) (proj₁ restTL)
        minTL = ++⁻ˡ (proj₁ restTL) p
          where
            open import Data.List.All.Properties
            
            p : All (inj₂ h' <P_) ((proj₁ restTL) ++ (proj₁ restTR))
            p rewrite PE.sym rest-concat = min    
     
   
        restTL-empty : (proj₁ restTL) ≡ []
        restTL-empty with keep (proj₁ restTL)
        restTL-empty | ([]) , q = q
        restTL-empty | (inj₁ x' ∷ t) , q with p₁
          where
            p₀ : inj₁ x' ∈≡ proj₁ restTL
            p₀ rewrite q = here PE.refl 

            p₁ : inj₂ h' <P inj₁ x'
            p₁ = LA.lookup minTL {inj₁ x'} p₀
        restTL-empty | (inj₁ x' ∷ t) , q | ()
        restTL-empty | (inj₂ x' ∷ t) , q with pointwise∈⃖ (proj₁ restL) (proj₁ restTL) (inj₂ x') z rest-eql
          where
            z : inj₂ x' ∈≡ (proj₁ restTL)
            z rewrite q = here PE.refl
        restTL-empty | (inj₂ x' ∷ t) , q | b , inj₂x'≡inj₁b =
          ⊥-elim $ inj-clash b x' (PE.sym inj₂x'≡inj₁b)
  
        minR : All (h' <R₀_) (proj₁ restR)
        minR =
          pointwiseRespAll⃖ imp (proj₁ restR) (proj₁ restTR) p' rest-eqr
          where
            open import Data.List.All.Properties
            
            p : All (inj₂ h' <P_) ((proj₁ restTL) ++ (proj₁ restTR))
            p rewrite PE.sym rest-concat = min 
            
            p' : All (inj₂ h' <P_) (proj₁ restTR)
            p' = ++⁻ʳ (proj₁ restTL) p
            
            imp : {a : |R₀|} → {b : |P|} → (inj₂ h' <P b) → (b ≡ inj₂ a) → (h' <R₀ a)
            imp {a} {b} (₂∼₂ h'<a) b≡inj₂a@PE.refl = h'<a
 
        minTR : All (inj₂ h' <P_) (proj₁ restTR)
        minTR = ++⁻ʳ (proj₁ restTL) p
          where
            open import Data.List.All.Properties
            
            p : All (inj₂ h' <P_) ((proj₁ restTL) ++ (proj₁ restTR))
            p rewrite PE.sym rest-concat = min     
        
        incompR : ¬ Any (h' ∦R₀_) (proj₁ restR)
        incompR h'∦restR = ⊥-elim $ incomp p'
          where
            open import Data.List.Any.Properties

            imp : {a : |R₀|} → {b : |P|} → h' ∦R₀ a → b ≡ inj₂ a → (inj₂ h') ∦P b
            imp {a} {b} (inj₁ h'⊑a) b≡inj₁a@PE.refl = inj₁ (₂∼₂ h'⊑a)
            imp {a} {b} (inj₂ a⊑h') b≡inj₁a@PE.refl = inj₂ (₂∼₂ a⊑h')

            p : Any (inj₂ h' ∦P_) (proj₁ restTR)
            p = pointwiseRespAny imp (proj₁ restR) (proj₁ restTR) h'∦restR rest-eqr

            p' : Any (inj₂ h' ∦P_) t
            p' = PE.subst (λ · → Any (inj₂ h' ∦P_) ·) (PE.sym rest-concat) (++⁺ʳ (proj₁ restTL) p) 
            
        incompTR : ¬ Any (inj₂ h' ∦P_) (proj₁ restTR)
        incompTR inj₂h'∦restTR = ⊥-elim $ incomp p'
          where
            open import Data.List.Any.Properties

            p' : Any (inj₂ h' ∦P_) t
            p' = PE.subst (λ · → Any (inj₂ h' ∦P_) ·) (PE.sym rest-concat) (++⁺ʳ (proj₁ restTL) inj₂h'∦restTR) 

    decompL : Carrier-FP → Carrier-FPL
    decompL a with decompose a
    decompL a | l , r , tl , tr , eql , eqr , concat =
      l

    decompR : Carrier-FP → Carrier-FPR
    decompR a with decompose a
    decompR a | l , r , tl , tr , eql , eqr , concat =
      r

{-
    a≈b→aL≈bL : (a b : Carrier-FP) → a ≈F b → (decompL a) ≈FL (decompL b)
    a≈b→aL≈bL a b a≈b with decompose a | decompose b
    a≈b→aL≈bL (.(atl ++ atr) , _) (.(btl ++ btr) , _) ((atl ++ atr) ≈F (btl ++ btr))  
               | al , ar , atl , atr , aeql , aeqr , aconcat 
               | bl , br , btl , btr , beql , beqr , bconcat =
      ?
  -}
              
    |g| : Carrier-FP → Carrier'
    |g| c with decompose c
    |g| c | l , r , tl , tr , eql , eqr , concat = 
      (|gL| l , |gR| r)


    inv-S→FP→S : (a : Carrier') → ((|g| $ |f| a) ≈' a)
    inv-S→FP→S (aL , aR) with decompose $ |f| (aL , aR)
    inv-S→FP→S (aL , aR) | l , r , atl , atr , aeql , aeqr , aconcat =
      eq1 , eq2
      where
        aconcat' : proj₁ (|f| $ aL , aR) ≡ (proj₁ atl ++ proj₁ atr)
        aconcat' = aconcat

        invaux-S→FP→S : (x : |P|) → (x ∈P (|f| $ aL , aR)) ⇔ (P-|f| (aL , aR) x)
        invaux-S→FP→S x = |f|-prop (aL , aR) x
        
        fLaL≈l : |fL| aL ≈FL l
        fLaL≈l = ≈FL-sym {l} {|fL| aL} (E.from ⟨$⟩ x∈l⇔x∈fLaL)
          where
            module E = Equivalence (c1≈c2⇔sameElementsL l (|fL| aL))  
            p→ : (x : |L₀|) → (x ∈L |fL| aL) → (x ∈L l)
            p→ x x∈fLaL = pointwiseRespAny⃖ imp (proj₁ l) (proj₁ atl) inj₁x∈atl aeql 
              where 
                inj₁x∈fa : (inj₁ x) ∈P |f| (aL , aR)
                inj₁x∈fa = from ⟨$⟩ (inj₁ $ x , ≈P-refl , x∈fLaL)
                  where
                    open Equivalence (invaux-S→FP→S $ inj₁ x)
                
                inj₁x∈atl++atr : (inj₁ x) ∈P' ((proj₁ atl) ++ (proj₁ atr))
                inj₁x∈atl++atr rewrite (PE.sym aconcat) = inj₁x∈fa 
 
                inj₁x∈atl : (inj₁ x) ∈P' (proj₁ atl)
                inj₁x∈atl with ∈-++⁻ ≈P-setoid (proj₁ atl) inj₁x∈atl++atr 
                  where
                    open import Data.List.Membership.Setoid.Properties
                inj₁x∈atl | inj₁ inj₁x∈atl = inj₁x∈atl
                inj₁x∈atl | inj₂ inj₁x∈atr = 
                  ⊥-elim $ (from ⟨$⟩ pointwiseRespAny⃖ imp (proj₁ r) (proj₁ atr) inj₁x∈atr aeqr)  
                  where
                    open import Data.List.Any.Properties
                    open Inverse ⊥↔Any⊥
                    imp : {a : |P|} → {b : |R₀|} → (inj₁ x ≈P a) → (a ≡ inj₂ b) → const ⊥ |R₀|
                    imp {a} {b} inj₁x≈a a≡inj₂b with ≈P-trans inj₁x≈a (≈P-reflexive a≡inj₂b)
                    imp {a} {b} inj₁x≈a a≡inj₂b | (₁∼₂ ())
                
                imp : ∀ {a : |P|} → {b : |L₀|} → (inj₁ x ≈P a) → (a ≡ inj₁ b) → (x ≈L₀ b)
                imp {a} {b} inj₁x≈a a≡inj₁b with ≈P-trans inj₁x≈a (≈P-reflexive a≡inj₁b)
                imp {a} {b} inj₁x≈a a≡inj₁b | (₁∼₁ x≈b) = x≈b

            p← : (x : |L₀|) → (x ∈L l) → (x ∈L |fL| aL)
            p← x x∈l with to ⟨$⟩ inj₁x∈fa 
              where
                open Equivalence (|f|-prop (aL , aR) (inj₁ x))  
                inj₁x∈atl : (inj₁ x) ∈P' (proj₁ atl)
                inj₁x∈atl = pointwiseRespAny imp (proj₁ l) (proj₁ atl) x∈l aeql 
                  where
                    imp : ∀ {a b} → (x ≈L₀ a) → (b ≡ inj₁ a) → (inj₁ x ≈P b)
                    imp {a} {b} x≈a b≡inj₁a = ≈P-trans (₁∼₁ x≈a) (≈P-reflexive $ PE.sym b≡inj₁a)
                inj₁x∈fa : (inj₁ x) ∈P (|f| $ aL , aR)
                inj₁x∈fa rewrite aconcat = ∈-++⁺ˡ ≈P-setoid inj₁x∈atl 
                  where
                    open import Data.List.Membership.Setoid.Properties
            p← x x∈l | inj₁ (l₀ , (₁∼₁ x≈l₀) , l₀∈fLaL) =
              LAny.map (λ l₀≈· → ≈L₀-trans x≈l₀ l₀≈·) l₀∈fLaL  
            p← x x∈l | inj₂ (r₀ , (₁∼₂ ()) , r₀∈fRaR)
            
            x∈l⇔x∈fLaL : (x : |L₀|) → (x ∈L l) ⇔ x ∈L (|fL| aL)
            x∈l⇔x∈fLaL x = equivalence (p← x) (p→ x)

        fRaR≈r : |fR| aR ≈FR r
        fRaR≈r = ≈FR-sym {r} {|fR| aR} (E.from ⟨$⟩ x∈r⇔x∈fRaR)
          where
            module E = Equivalence (c1≈c2⇔sameElementsR r (|fR| aR))  
            p→ : (x : |R₀|) → (x ∈R |fR| aR) → (x ∈R r)
            p→ x x∈fRaR = pointwiseRespAny⃖ imp (proj₁ r) (proj₁ atr) inj₂x∈atr aeqr 
              where 
                inj₂x∈fa : (inj₂ x) ∈P |f| (aL , aR)
                inj₂x∈fa = from ⟨$⟩ (inj₂ $ x , ≈P-refl , x∈fRaR)
                  where
                    open Equivalence (invaux-S→FP→S $ inj₂ x)
                
                inj₂x∈atl++atr : (inj₂ x) ∈P' ((proj₁ atl) ++ (proj₁ atr))
                inj₂x∈atl++atr rewrite (PE.sym aconcat) = inj₂x∈fa 
 
                inj₂x∈atr : (inj₂ x) ∈P' (proj₁ atr)
                inj₂x∈atr with ∈-++⁻ ≈P-setoid (proj₁ atl) inj₂x∈atl++atr 
                  where
                    open import Data.List.Membership.Setoid.Properties
                inj₂x∈atr | inj₁ inj₂x∈atl = 
                  ⊥-elim $ (from ⟨$⟩ pointwiseRespAny⃖ imp (proj₁ l) (proj₁ atl) inj₂x∈atl aeql)  
                  where
                    open import Data.List.Any.Properties
                    open Inverse ⊥↔Any⊥
                    imp : {a : |P|} → {b : |L₀|} → (inj₂ x ≈P a) → (a ≡ inj₁ b) → const ⊥ |R₀|
                    imp {a} {b} inj₂x≈a a≡inj₂b with ≈P-trans inj₂x≈a (≈P-reflexive a≡inj₂b)
                    imp {a} {b} inj₂x≈a a≡inj₂b | ()
                inj₂x∈atr | inj₂ inj₂x∈atr = inj₂x∈atr
                
                imp : ∀ {a : |P|} → {b : |R₀|} → (inj₂ x ≈P a) → (a ≡ inj₂ b) → (x ≈R₀ b)
                imp {a} {b} inj₂x≈a a≡inj₂b with ≈P-trans inj₂x≈a (≈P-reflexive a≡inj₂b)
                imp {a} {b} inj₂x≈a a≡inj₂b | (₂∼₂ x≈b) = x≈b

            p← : (x : |R₀|) → (x ∈R r) → (x ∈R |fR| aR)
            p← x x∈r with to ⟨$⟩ inj₂x∈fa 
              where
                open Equivalence (|f|-prop (aL , aR) (inj₂ x))  
                inj₂x∈atr : (inj₂ x) ∈P' (proj₁ atr)
                inj₂x∈atr = pointwiseRespAny imp (proj₁ r) (proj₁ atr) x∈r aeqr 
                  where
                    imp : ∀ {a b} → (x ≈R₀ a) → (b ≡ inj₂ a) → (inj₂ x ≈P b)
                    imp {a} {b} x≈a b≡inj₂a = ≈P-trans (₂∼₂ x≈a) (≈P-reflexive $ PE.sym b≡inj₂a)
                inj₂x∈fa : (inj₂ x) ∈P (|f| $ aL , aR)
                inj₂x∈fa rewrite aconcat = ∈-++⁺ʳ ≈P-setoid (proj₁ atl) inj₂x∈atr 
                  where
                    open import Data.List.Membership.Setoid.Properties
            p← x x∈l | inj₁ (l₀ , () , l₀∈fLaL)
            p← x x∈l | inj₂ (r₀ , (₂∼₂ x≈r₀) , r₀∈fRaR) =
              LAny.map (λ r₀≈· → ≈R₀-trans x≈r₀ r₀≈·) r₀∈fRaR  
            
            x∈r⇔x∈fRaR : (x : |R₀|) → (x ∈R r) ⇔ x ∈R (|fR| aR)
            x∈r⇔x∈fRaR x = equivalence (p← x) (p→ x)
                           
        eq1 : |gL| l ≈L aL
        eq1 = 
          begin
            |gL| l ≈⟨ |gL|-≈ l (|fL| aL) (≈FL-sym {|fL| aL} {l} fLaL≈l) ⟩
            |gL| (|fL| aL) ≈⟨ |gL|-inv-S→FP→S aL ⟩
            aL
           ∎
          where
            open import Relation.Binary.EqReasoning ≈L-setoid

        eq2 : |gR| r ≈R aR
        eq2 = 
          begin
            |gR| r ≈⟨ |gR|-≈ r (|fR| aR) (≈FR-sym {|fR| aR} {r} fRaR≈r) ⟩
            |gR| (|fR| aR) ≈⟨ |gR|-inv-S→FP→S aR ⟩
            aR
           ∎
          where
            open import Relation.Binary.EqReasoning ≈R-setoid 

    -- inv-FP→S→FP : (a : BoundedJoinSemilattice.Carrier $ FP P) → (BoundedJoinSemilattice._≈_ (FP P) (proj₁ f $ proj₁ g $ a) a) 


{-
    |g|-≈ : (a b : Carrier-FP) → (a ≈F b) → (|g| a) ≈' (|g| b)
    |g|-≈ (.[] , []-Free) (.[] , []-Free) [] =
      |gL|-≈ ([] , []-FreeL) ([] , []-FreeL) [] , |gR|-≈ ([] , []-FreeR) ([] , []-FreeR) [] 
    |g|-≈ ((inj₁ ha) ∷ ta) , _) ((inj₁ hb) ∷ tb , _) (x∼y ∷ ta≈tb) = {!!}
  -}   
{-
|g|-≈ a b a≈b with decompose a | decompose b | Pointwise-length a≈b
    |g|-≈ (.(atl ++ atr) , _) (.(btl ++ btr) , _) a≈b  
          | al , ar , (atl , _) , (atr , _) , aeql , aeqr , PE.refl 
          | bl , br , (btl , _) , (btr , _) , beql , beqr , PE.refl
          | lena≡lenb = 
      {!!}
-}      
        
⟦ IVarSemilat x ⁂⟧ = {!!}
⟦ PartialSemilat x ⁂⟧ = {!!}
