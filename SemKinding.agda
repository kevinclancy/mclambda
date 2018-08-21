module SemKinding where

open import Function using (_$_ ; _|>′_)
open import Syntax
open import Kinding
open import BoolPoset
open import Relation.Nullary
open import Relation.Binary
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.List
open import Data.List.Any as LAny
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
  ; g = {!!} , {!!} , {!!}
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
    _≈R_ = BoundedJoinSemilattice._≈_ bjsR
    ≈R-refl = BoundedJoinSemilattice.Eq.refl bjsR
    ≈R-sym = BoundedJoinSemilattice.Eq.sym bjsR

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
    _≈R₀_ : |R₀| → |R₀| → Set
    _≈R₀_ = DeltaPoset._≈_ deltaR
    ≈R₀-sym = DeltaPoset.sym≈ deltaR
    ≈R₀-refl = DeltaPoset.refl≈ deltaR
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
       ≈-sym to ≈F-sym ; ∨-congˡ to ∨F-congˡ ; ∨-congʳ to ∨F-congʳ ; ∨-assoc to ∨F-assoc ; ∨-comm to ∨F-comm ) 
    open import FreeSemilattice deltaL renaming 
      (IsFreeList to IsFreeListL ; []-Free to []-FreeL ; ∷-Free to ∷-FreeL ; _≈_ to _≈FL_ ; ⊥ to ⊥FL ; 
       SemilatCarrier to Carrier-FPL ; _∨_ to _∨FL_ ; FP-BJS to FPL-BJS ; FP-setoid to FPL-setoid ;
       ∨-identityˡ to ∨FL-identityˡ ; ∨-identityʳ to ∨FL-identityʳ ; ⊑-refl to ⊑L₀-refl ; ⊑-reflexive to ⊑L₀-reflexive ;
       sng-free to sng-freeL ; _≤_ to _≤FL_ ; ≈-sym to ≈FL-sym )
    open import FreeSemilattice deltaR renaming 
      (IsFreeList to IsFreeListR ; []-Free to []-FreeR ; ∷-Free to ∷-FreeR ; _≈_ to _≈FR_ ; ⊥ to ⊥FR ; 
       SemilatCarrier to Carrier-FPR ; _∨_ to _∨FR_ ; FP-BJS to FPR-BJS ; FP-setoid to FPL-setoid ;
       ∨-identityˡ to ∨FR-identityˡ ; ∨-identityʳ to ∨FR-identityʳ ; ⊑-refl to ⊑L₀-refl ; ⊑-reflexive to ⊑R₀-reflexive ;
       sng-free to sng-freeR ; _≤_ to _≤FR_ ; ≈-sym to ≈FR-sym)

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

    gR = SemSemilat.g semSemilatR

    |gR| : Carrier-FPR → |R|
    |gR| = proj₁ $ SemSemilat.g semSemilatR

    |gR|-≈ : (a b : Carrier-FPR) → a ≈FR b → (|gR| a) ≈R (|gR| b) 
    |gR|-≈ = proj₁ $ proj₂ $ SemSemilat.g semSemilatR

    |gR|-⊥ : (|gR| ⊥FR) ≈R ⊥R
    |gR|-⊥ = proj₁ $ proj₂ $ proj₂ $ SemSemilat.g semSemilatR

    |gR|-∨ : ∀ (a b : Carrier-FPR) → |gR| (a ∨FR b) ≈R ( (|gR| a) ∨R (|gR| b) ) 
    |gR|-∨ = proj₂ $ proj₂ $ proj₂ $ SemSemilat.g semSemilatR


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

    |f| : Carrier' → Carrier-FP
    |f| (aL , aR) =
      (resL-list , resL-free) ∨F (resR-list , resR-free) 
      where
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
    |g| : Carrier-FP → Carrier'
    |g| ([] , []-Free) = ⊥'
    |g| ((inj₁ h') ∷ t , ∷-Free _ _ _ _ ft) = (|gL| (h' ∷ [] , sng-freeL) , ⊥R) ∨' (|g| $ t , ft)
    |g| ((inj₂ h') ∷ t , ∷-Free _ _ _ _ ft) = (⊥L , |gR| (h' ∷ [] , sng-freeR)) ∨' (|g| $ t , ft)

    |g|-≈ : (a b : Carrier-FP) → (a ≈F b) → (|g| a) ≈' (|g| b)  
    |g|-≈ ([] , []-Free) ([] , []-Free) [] = ≈'-refl
    |g|-≈ ([] , fa) (hb ∷ tb , fb) ()
    |g|-≈ (ha ∷ ta , fa) ([] , fb) ()
    |g|-≈ a@((inj₁ ha) ∷ ta , ∷-Free _ _ _ _ fta) b@((inj₁ hb) ∷ tb , ∷-Free _ _ _ _ ftb) ((₁∼₁ ha~hb) ∷ ta≈tb) = 
      let
        h : (ha ∷ [] , sng-freeL) ≈FL (hb ∷ [] , sng-freeL)
        h = ha~hb ∷ []
      in
      begin 
        (|g| a) ≡⟨ PE.refl ⟩
        (|gL| (ha ∷ [] , sng-freeL) , ⊥R) ∨' (|g| $ ta , fta) ≈⟨ ∨-cong ((|gL|-≈ (ha ∷ [] , sng-freeL) (hb ∷ [] , sng-freeL) h , ≈R-refl)) (|g|-≈ (ta , fta) (tb , ftb) ta≈tb) ⟩ 
        (|gL| (hb ∷ [] , sng-freeL) , ⊥R) ∨' (|g| $ tb , ftb) ≡⟨ PE.refl ⟩
        (|g| b)
       ∎
      where
        open import Relation.Binary.Properties.JoinSemilattice joinSemilatticeS
        open import Relation.Binary.EqReasoning ≈'-setoid 
    |g|-≈ a@((inj₂ ha) ∷ ta , ∷-Free _ _ _ _ fta) b@((inj₂ hb) ∷ tb , ∷-Free _ _ _ _ ftb) ((₂∼₂ ha~hb) ∷ ta≈tb) =
      let
        h : (ha ∷ [] , sng-freeR) ≈FR (hb ∷ [] , sng-freeR)
        h = ha~hb ∷ []
      in
      begin 
        (|g| a) ≡⟨ PE.refl ⟩
        (⊥L , |gR| (ha ∷ [] , sng-freeR) ) ∨' (|g| $ ta , fta) ≈⟨ ∨-cong ((≈L-refl , |gR|-≈ (ha ∷ [] , sng-freeR) (hb ∷ [] , sng-freeR) h)) (|g|-≈ (ta , fta) (tb , ftb) ta≈tb) ⟩ 
        (⊥L , |gR| (hb ∷ [] , sng-freeR) ) ∨' (|g| $ tb , ftb) ≡⟨ PE.refl ⟩
        (|g| b)
       ∎
      where
        open import Relation.Binary.Properties.JoinSemilattice joinSemilatticeS
        open import Relation.Binary.EqReasoning ≈'-setoid 
    |g|-≈ a@((inj₁ ha) ∷ ta , ∷-Free _ _ _ _ fta) b@((inj₂ hb) ∷ tb , ∷-Free _ _ _ _ ftb) ((₁∼₂ ()) ∷ ta≈tb)

    |g|-⊥ : |g| ⊥F ≈' ⊥'
    |g|-⊥ = ≈'-refl

    |g|-∨ : (a b : Carrier-FP) → (|g| $ a ∨F b) ≈' ((|g| a) ∨' (|g| b))
    |g|-∨ ([] , []-Free) ([] , []-Free) = 
      begin
        (|g| $ ([] , []-Free) ∨F ([] , []-Free)) ≈⟨ |g|-≈ (([] , []-Free) ∨F ([] , []-Free)) ([] , []-Free) $ ∨F-identityˡ ([] , []-Free) ⟩
        (|g| $ ([] , []-Free)) ≈⟨ |g|-⊥ ⟩
        ⊥' ≈⟨ ≈'-sym $ identityˡ ⊥' ⟩ 
        (⊥' ∨' ⊥')
       ∎
      where
        open import Relation.Binary.EqReasoning (≈'-setoid)
        open import Relation.Binary.Properties.BoundedJoinSemilattice S
    |g|-∨ a@([] , []-Free) b@(hb ∷ tb , ∷-Free _ _ _ _ ftb) =
      begin
        (|g| $ ([] , []-Free) ∨F b) ≈⟨ |g|-≈ (([] , []-Free) ∨F b) b $ ∨F-identityˡ b ⟩
        (|g| b) ≈⟨ ≈'-sym $ identityˡ (|g| b) ⟩
        ⊥' ∨' (|g| b) ≈⟨ ∨-cong (≈'-sym |g|-⊥) ≈'-refl  ⟩
        (|g| ([] , []-Free)) ∨' (|g| b)
       ∎
      where
        open import Relation.Binary.EqReasoning (≈'-setoid)
        open import Relation.Binary.Properties.BoundedJoinSemilattice S
        open import Relation.Binary.Properties.JoinSemilattice (BoundedJoinSemilattice.joinSemiLattice S)
    |g|-∨ a@(ha ∷ ta , ∷-Free _ _ _ _ fta) b@([] , []-Free) =
      begin
        (|g| $ a ∨F ([] , []-Free)) ≈⟨ ≈'-sym $ |g|-≈ (a ∨F ([] , []-Free)) a $ ∨F-identityˡ a ⟩
        (|g| a) ≈⟨ ≈'-sym $ identityʳ (|g| a) ⟩
        (|g| a) ∨' ⊥' ≈⟨ ∨-cong ≈'-refl (≈'-sym |g|-⊥) ⟩
        (|g| a) ∨' (|g| ([] , []-Free)) 
       ∎
      where
        open import Relation.Binary.EqReasoning (≈'-setoid)
        open import Relation.Binary.Properties.BoundedJoinSemilattice S
        open import Relation.Binary.Properties.JoinSemilattice (BoundedJoinSemilattice.joinSemiLattice S)
    |g|-∨ (ha ∷ ta , fa@(∷-Free _ _ _ _ fta)) (hb ∷ tb , fb@(∷-Free _ _ _ _ ftb)) with ha ∦P? hb
    |g|-∨ a@((inj₁ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₂ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l⊑r (₁∼₂ ()) ¬hb⊑ha 
    |g|-∨ a@((inj₂ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₁ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l⊑r () ¬hb⊑ha
    |g|-∨ a@((inj₁ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₁ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l⊑r (₁∼₁ ha⊑hb) ¬hb⊑ha = 
      begin
        (|g| $ (ta , fta) ∨F b) ≈⟨ |g|-∨ (ta , fta) b ⟩
        (|g| $ ta , fta) ∨' (|g| b) ≡⟨ PE.refl ⟩
        (|g| $ ta , fta) ∨' ((|gL| sngB , ⊥R) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong p ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ((|gL| (sngA ∨FL sngB) , ⊥R) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong (|gL|-∨ sngA sngB , ≈R-refl) ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ( ((|gL| sngA) ∨L (|gL| sngB) , ⊥R) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong (≈L-refl , (≈R-sym $ R-identityʳ ⊥R)) ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ( ((|gL| sngA) ∨L (|gL| sngB) , ⊥R ∨R ⊥R) ∨' (|g| $ tb , ftb))  ≡⟨ PE.refl ⟩ 
        (|g| $ ta , fta) ∨' ( ((|gL| sngA , ⊥R) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ tb , ftb) ) ≈⟨ ≈'-sym $ ∨'-assoc (|g| $ ta , fta) ((|gL| sngA , ⊥R) ∨' (|gL| sngB , ⊥R)) (|g| $ tb , ftb) ⟩ 
        ((|g| $ ta , fta) ∨' (|gL| sngA , ⊥R) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ tb , ftb) ≈⟨ ∨-cong (≈'-sym $ ∨'-assoc (|g| $ ta , fta) (|gL| sngA , ⊥R) (|gL| sngB , ⊥R)) ≈'-refl ⟩
        (((|g| $ ta , fta) ∨' (|gL| sngA , ⊥R)) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ tb , ftb) ≈⟨ ∨-cong  (∨-cong (∨'-comm (|g| $ ta , fta) (|gL| sngA , ⊥R)) ≈'-refl) ≈'-refl  ⟩
        (((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-assoc ((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) (|gL| sngB , ⊥R) (|g| $ tb , ftb)  ⟩ 
        ((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) ∨' ((|gL| sngB , ⊥R) ∨' (|g| $ tb , ftb)) ≡⟨ PE.refl ⟩
        (|g| $ a) ∨' (|g| b)
       ∎
      where
        jsS = BoundedJoinSemilattice.joinSemiLattice S

        open import Relation.Binary.EqReasoning (≈'-setoid)
        open import Relation.Binary.Properties.BoundedJoinSemilattice S
        open import Relation.Binary.Properties.JoinSemilattice jsS
          renaming( ∨-assoc to ∨'-assoc ; ∨-comm to ∨'-comm )
        open import Relation.Binary.Properties.BoundedJoinSemilattice bjsR
          renaming (identityˡ to R-identityˡ ; identityʳ to R-identityʳ)

        |gL|-mono = ⇉-mono {S = FPL-BJS} {T = SemSemilat.S semSemilatL} gL

        sngA = (ha ∷ [] , sng-freeL)
        sngB = (hb ∷ [] , sng-freeL)

        h : sngA ≤FL sngB 
        h = (here ha⊑hb) ∷ []

        p : (|gL| sngB , ⊥R) ≈' ((|gL| $ sngA ∨FL sngB) , ⊥R) 
        p = ( (|gL|-≈ sngB (sngA ∨FL sngB) $ ≈FL-sym {sngA ∨FL sngB} {sngB} (connecting→ {A = BoundedJoinSemilattice.joinSemiLattice FPL-BJS} sngA sngB h)) , ≈R-refl) 
    |g|-∨ a@((inj₂ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₂ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l⊑r (₂∼₂ ha⊑hb) ¬hb⊑ha = 
      begin
        (|g| $ (ta , fta) ∨F b) ≈⟨ |g|-∨ (ta , fta) b ⟩
        (|g| $ ta , fta) ∨' (|g| b) ≡⟨ PE.refl ⟩
        (|g| $ ta , fta) ∨' ((⊥L , |gR| sngB) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong p ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ((⊥L , |gR| (sngA ∨FR sngB)) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong (≈L-refl , |gR|-∨ sngA sngB) ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ( (⊥L , (|gR| sngA) ∨R (|gR| sngB)) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong ((≈L-sym $ L-identityʳ ⊥L) , ≈R-refl) ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ( (⊥L ∨L ⊥L , (|gR| sngA) ∨R (|gR| sngB)) ∨' (|g| $ tb , ftb))  ≡⟨ PE.refl ⟩ 
        (|g| $ ta , fta) ∨' (((⊥L , |gR| sngA) ∨' (⊥L , |gR| sngB) ) ∨' (|g| $ tb , ftb)) ≈⟨ ≈'-sym $ ∨'-assoc (|g| $ ta , fta) ((⊥L , |gR| sngA) ∨' (⊥L , |gR| sngB)) (|g| $ tb , ftb) ⟩ 
        ((|g| $ ta , fta) ∨' (⊥L , |gR| sngA) ∨' (⊥L , |gR| sngB)) ∨' (|g| $ tb , ftb) ≈⟨ ∨-cong (≈'-sym $ ∨'-assoc (|g| $ ta , fta) (⊥L , |gR| sngA) (⊥L , |gR| sngB)) ≈'-refl ⟩
        (((|g| $ ta , fta) ∨' (⊥L , |gR| sngA)) ∨' (⊥L , |gR| sngB)) ∨' (|g| $ tb , ftb) ≈⟨ ∨-cong  (∨-cong (∨'-comm (|g| $ ta , fta) (⊥L , |gR| sngA)) ≈'-refl) ≈'-refl  ⟩
        (((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) ∨' (⊥L , |gR| sngB)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-assoc ((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) (⊥L , |gR| sngB) (|g| $ tb , ftb)  ⟩ 
        ((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) ∨' ((⊥L , |gR| sngB) ∨' (|g| $ tb , ftb)) ≡⟨ PE.refl ⟩
        (|g| $ a) ∨' (|g| b)
       ∎
      where
        jsS = BoundedJoinSemilattice.joinSemiLattice S

        open import Relation.Binary.EqReasoning (≈'-setoid)
        open import Relation.Binary.Properties.BoundedJoinSemilattice S
        open import Relation.Binary.Properties.JoinSemilattice jsS
          renaming( ∨-assoc to ∨'-assoc ; ∨-comm to ∨'-comm )
        open import Relation.Binary.Properties.BoundedJoinSemilattice bjsL
          renaming (identityˡ to L-identityˡ ; identityʳ to L-identityʳ)

        sngA = (ha ∷ [] , sng-freeR)
        sngB = (hb ∷ [] , sng-freeR)

        h : sngA ≤FR sngB 
        h = (here ha⊑hb) ∷ []

        p : (⊥L , |gR| sngB) ≈' (⊥L , (|gR| $ sngA ∨FR sngB)) 
        p = ( ≈L-refl , (|gR|-≈ sngB (sngA ∨FR sngB) $ ≈FR-sym {sngA ∨FR sngB} {sngB} (connecting→ {A = BoundedJoinSemilattice.joinSemiLattice FPR-BJS} sngA sngB h)) ) 
    |g|-∨ a@((inj₁ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₂ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | r⊑l ¬ha⊑hb ()
    |g|-∨ a@((inj₂ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₁ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | r⊑l ¬ha⊑hb (₁∼₂ ())
    |g|-∨ a@((inj₁ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₁ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | r⊑l ¬ha⊑hb (₁∼₁ hb⊑ha) =
      begin
        (|g| $ a ∨F (tb , ftb)) ≈⟨ |g|-∨ a (tb , ftb) ⟩
        (|g| $ a) ∨' (|g| $ tb , ftb) ≡⟨ PE.refl ⟩
        ((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-cong p ≈'-refl) ≈'-refl ⟩
        ((|gL| (sngB ∨FL sngA) , ⊥R) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-cong (|gL|-∨ sngB sngA , ≈R-refl) ≈'-refl) ≈'-refl ⟩ 
        (((|gL| sngB) ∨L (|gL| sngA) , ⊥R) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-cong (≈L-refl , (≈R-sym $ R-identityʳ ⊥R)) ≈'-refl) ≈'-refl ⟩ 
        (((|gL| sngB) ∨L (|gL| sngA) , ⊥R ∨R ⊥R) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≡⟨ PE.refl ⟩
        (((|gL| sngB , ⊥R) ∨' (|gL| sngA , ⊥R)) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≈⟨  ∨'-cong (∨'-cong (∨'-comm (|gL| sngB , ⊥R) (|gL| sngA , ⊥R)) ≈'-refl) ≈'-refl ⟩ 
        (((|gL| sngA , ⊥R) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-assoc (|gL| sngA , ⊥R) (|gL| sngB , ⊥R) (|g| $ ta , fta)) ≈'-refl ⟩ 
        ((|gL| sngA , ⊥R) ∨' ((|gL| sngB , ⊥R) ∨' (|g| $ ta , fta))) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-cong ≈'-refl (∨'-comm (|gL| sngB , ⊥R) (|g| $ ta , fta))) ≈'-refl ⟩
        ((|gL| sngA , ⊥R) ∨' ((|g| $ ta , fta) ∨' (|gL| sngB , ⊥R))) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (≈'-sym (∨'-assoc (|gL| sngA , ⊥R) (|g| $ ta , fta) (|gL| sngB , ⊥R))) ≈'-refl ⟩
        (((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ tb , ftb) ≈⟨  ∨'-assoc ((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) (|gL| sngB , ⊥R) (|g| $ tb , ftb)  ⟩ 
        ((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) ∨' ((|gL| sngB , ⊥R) ∨' (|g| $ tb , ftb)) ≡⟨ PE.refl ⟩ 
        (|g| $ a) ∨' (|g| b)
       ∎
      where
        jsS = BoundedJoinSemilattice.joinSemiLattice S

        open import Relation.Binary.EqReasoning (≈'-setoid)
        open import Relation.Binary.Properties.BoundedJoinSemilattice S
        open import Relation.Binary.Properties.JoinSemilattice jsS
          renaming( ∨-assoc to ∨'-assoc ; ∨-comm to ∨'-comm ; ∨-cong to ∨'-cong )
        open import Relation.Binary.Properties.BoundedJoinSemilattice bjsR
          renaming (identityˡ to R-identityˡ ; identityʳ to R-identityʳ)

        sngA = (ha ∷ [] , sng-freeL)
        sngB = (hb ∷ [] , sng-freeL)

        h : sngB ≤FL sngA 
        h = (here hb⊑ha) ∷ []

        p : (|gL| sngA , ⊥R) ≈' ((|gL| $ sngB ∨FL sngA) , ⊥R) 
        p = ( (|gL|-≈ sngA (sngB ∨FL sngA) $ ≈FL-sym {sngB ∨FL sngA} {sngA} (connecting→ {A = BoundedJoinSemilattice.joinSemiLattice FPL-BJS} sngB sngA h)) , ≈R-refl)       
    |g|-∨ a@((inj₂ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₂ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | r⊑l ¬ha⊑hb (₂∼₂ hb⊑ha) =
      begin
        (|g| $ a ∨F (tb , ftb)) ≈⟨ |g|-∨ a (tb , ftb) ⟩
        (|g| $ a) ∨' (|g| $ tb , ftb) ≡⟨ PE.refl ⟩
        ((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-cong p ≈'-refl) ≈'-refl ⟩
        ((⊥L , |gR| (sngB ∨FR sngA)) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-cong (≈L-refl , |gR|-∨ sngB sngA) ≈'-refl) ≈'-refl ⟩ 
        (((⊥L , (|gR| sngB) ∨R (|gR| sngA))) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-cong ((≈L-sym $ L-identityʳ ⊥L) , ≈R-refl) ≈'-refl) ≈'-refl ⟩ 
        ((⊥L ∨L ⊥L , (|gR| sngB) ∨R (|gR| sngA)) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≡⟨ PE.refl ⟩
        (((⊥L , |gR| sngB) ∨' (⊥L , |gR| sngA)) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≈⟨  ∨'-cong (∨'-cong (∨'-comm (⊥L , |gR| sngB) (⊥L , |gR| sngA)) ≈'-refl) ≈'-refl ⟩ 
        (((⊥L , |gR| sngA) ∨' (⊥L , |gR| sngB)) ∨' (|g| $ ta , fta)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-assoc (⊥L , |gR| sngA) (⊥L , |gR| sngB) (|g| $ ta , fta)) ≈'-refl ⟩ 
        ((⊥L , |gR| sngA) ∨' ((⊥L , |gR| sngB) ∨' (|g| $ ta , fta))) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-cong ≈'-refl (∨'-comm (⊥L , |gR| sngB) (|g| $ ta , fta))) ≈'-refl ⟩
        ((⊥L , |gR| sngA) ∨' ((|g| $ ta , fta) ∨' (⊥L , |gR| sngB))) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (≈'-sym (∨'-assoc (⊥L , |gR| sngA) (|g| $ ta , fta) (⊥L , |gR| sngB))) ≈'-refl ⟩
        (((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) ∨' (⊥L , |gR| sngB)) ∨' (|g| $ tb , ftb) ≈⟨  ∨'-assoc ((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) (⊥L , |gR| sngB) (|g| $ tb , ftb)  ⟩ 
        ((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) ∨' ((⊥L , |gR| sngB) ∨' (|g| $ tb , ftb)) ≡⟨ PE.refl ⟩ 
        (|g| $ a) ∨' (|g| b) 
       ∎
      where
        jsS = BoundedJoinSemilattice.joinSemiLattice S

        open import Relation.Binary.EqReasoning (≈'-setoid)
        open import Relation.Binary.Properties.BoundedJoinSemilattice S
        open import Relation.Binary.Properties.JoinSemilattice jsS
          renaming( ∨-assoc to ∨'-assoc ; ∨-comm to ∨'-comm ; ∨-cong to ∨'-cong )
        open import Relation.Binary.Properties.BoundedJoinSemilattice bjsL
          renaming (identityˡ to L-identityˡ ; identityʳ to L-identityʳ)

        sngA = (ha ∷ [] , sng-freeR)
        sngB = (hb ∷ [] , sng-freeR)

        h : sngB ≤FR sngA 
        h = (here hb⊑ha) ∷ []

        p : (⊥L , |gR| sngA) ≈' (⊥L , (|gR| $ sngB ∨FR sngA)) 
        p = (≈L-refl , (|gR|-≈ sngA (sngB ∨FR sngA) $ ≈FR-sym {sngB ∨FR sngA} {sngA} (connecting→ {A = BoundedJoinSemilattice.joinSemiLattice FPR-BJS} sngB sngA h)))       
    |g|-∨ a@((inj₁ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₂ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l≈r (₁∼₂ ())
    |g|-∨ a@((inj₂ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₁ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l≈r ()
    |g|-∨ a@((inj₁ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₁ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l≈r (₁∼₁ ha≈hb) =
      begin
        (|g| $ (ta , fta) ∨F b) ≈⟨ |g|-∨ (ta , fta) b ⟩
        (|g| $ ta , fta) ∨' (|g| b) ≡⟨ PE.refl ⟩
        (|g| $ ta , fta) ∨' ((|gL| sngB , ⊥R) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong p ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ((|gL| (sngA ∨FL sngB) , ⊥R) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong (|gL|-∨ sngA sngB , ≈R-refl) ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ( ((|gL| sngA) ∨L (|gL| sngB) , ⊥R) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong (≈L-refl , (≈R-sym $ R-identityʳ ⊥R)) ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ( ((|gL| sngA) ∨L (|gL| sngB) , ⊥R ∨R ⊥R) ∨' (|g| $ tb , ftb))  ≡⟨ PE.refl ⟩ 
        (|g| $ ta , fta) ∨' ( ((|gL| sngA , ⊥R) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ tb , ftb) ) ≈⟨ ≈'-sym $ ∨'-assoc (|g| $ ta , fta) ((|gL| sngA , ⊥R) ∨' (|gL| sngB , ⊥R)) (|g| $ tb , ftb) ⟩ 
        ((|g| $ ta , fta) ∨' (|gL| sngA , ⊥R) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ tb , ftb) ≈⟨ ∨-cong (≈'-sym $ ∨'-assoc (|g| $ ta , fta) (|gL| sngA , ⊥R) (|gL| sngB , ⊥R)) ≈'-refl ⟩
        (((|g| $ ta , fta) ∨' (|gL| sngA , ⊥R)) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ tb , ftb) ≈⟨ ∨-cong  (∨-cong (∨'-comm (|g| $ ta , fta) (|gL| sngA , ⊥R)) ≈'-refl) ≈'-refl  ⟩
        (((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-assoc ((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) (|gL| sngB , ⊥R) (|g| $ tb , ftb)  ⟩ 
        ((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) ∨' ((|gL| sngB , ⊥R) ∨' (|g| $ tb , ftb)) ≡⟨ PE.refl ⟩
        (|g| $ a) ∨' (|g| b)
       ∎
      where
        jsS = BoundedJoinSemilattice.joinSemiLattice S

        open import Relation.Binary.EqReasoning (≈'-setoid)
        open import Relation.Binary.Properties.BoundedJoinSemilattice S
        open import Relation.Binary.Properties.JoinSemilattice jsS
          renaming( ∨-assoc to ∨'-assoc ; ∨-comm to ∨'-comm )
        open import Relation.Binary.Properties.BoundedJoinSemilattice bjsR
          renaming (identityˡ to R-identityˡ ; identityʳ to R-identityʳ)

        sngA = (ha ∷ [] , sng-freeL)
        sngB = (hb ∷ [] , sng-freeL)

        h : sngA ≤FL sngB 
        h = (here (⊑L₀-reflexive ha≈hb)) ∷ []

        p : (|gL| sngB , ⊥R) ≈' ((|gL| $ sngA ∨FL sngB) , ⊥R) 
        p = ( (|gL|-≈ sngB (sngA ∨FL sngB) $ ≈FL-sym {sngA ∨FL sngB} {sngB} (connecting→ {A = BoundedJoinSemilattice.joinSemiLattice FPL-BJS} sngA sngB h)) , ≈R-refl) 
    |g|-∨ a@((inj₂ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₂ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l≈r (₂∼₂ ha≈hb) = 
      begin
        (|g| $ (ta , fta) ∨F b) ≈⟨ |g|-∨ (ta , fta) b ⟩
        (|g| $ ta , fta) ∨' (|g| b) ≡⟨ PE.refl ⟩
        (|g| $ ta , fta) ∨' ((⊥L , |gR| sngB) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong p ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ((⊥L , |gR| (sngA ∨FR sngB)) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong (≈L-refl , |gR|-∨ sngA sngB) ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ( (⊥L , (|gR| sngA) ∨R (|gR| sngB)) ∨' (|g| $ tb , ftb)) ≈⟨ ∨-cong ≈'-refl (∨-cong ((≈L-sym $ L-identityʳ ⊥L) , ≈R-refl) ≈'-refl) ⟩
        (|g| $ ta , fta) ∨' ( (⊥L ∨L ⊥L , (|gR| sngA) ∨R (|gR| sngB)) ∨' (|g| $ tb , ftb))  ≡⟨ PE.refl ⟩ 
        (|g| $ ta , fta) ∨' (((⊥L , |gR| sngA) ∨' (⊥L , |gR| sngB) ) ∨' (|g| $ tb , ftb)) ≈⟨ ≈'-sym $ ∨'-assoc (|g| $ ta , fta) ((⊥L , |gR| sngA) ∨' (⊥L , |gR| sngB)) (|g| $ tb , ftb) ⟩ 
        ((|g| $ ta , fta) ∨' (⊥L , |gR| sngA) ∨' (⊥L , |gR| sngB)) ∨' (|g| $ tb , ftb) ≈⟨ ∨-cong (≈'-sym $ ∨'-assoc (|g| $ ta , fta) (⊥L , |gR| sngA) (⊥L , |gR| sngB)) ≈'-refl ⟩
        (((|g| $ ta , fta) ∨' (⊥L , |gR| sngA)) ∨' (⊥L , |gR| sngB)) ∨' (|g| $ tb , ftb) ≈⟨ ∨-cong  (∨-cong (∨'-comm (|g| $ ta , fta) (⊥L , |gR| sngA)) ≈'-refl) ≈'-refl  ⟩
        (((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) ∨' (⊥L , |gR| sngB)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-assoc ((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) (⊥L , |gR| sngB) (|g| $ tb , ftb)  ⟩ 
        ((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) ∨' ((⊥L , |gR| sngB) ∨' (|g| $ tb , ftb)) ≡⟨ PE.refl ⟩
        (|g| $ a) ∨' (|g| b)
       ∎
      where
        jsS = BoundedJoinSemilattice.joinSemiLattice S

        open import Relation.Binary.EqReasoning (≈'-setoid)
        open import Relation.Binary.Properties.BoundedJoinSemilattice S
        open import Relation.Binary.Properties.JoinSemilattice jsS
          renaming( ∨-assoc to ∨'-assoc ; ∨-comm to ∨'-comm )
        open import Relation.Binary.Properties.BoundedJoinSemilattice bjsL
          renaming (identityˡ to L-identityˡ ; identityʳ to L-identityʳ)

        sngA = (ha ∷ [] , sng-freeR)
        sngB = (hb ∷ [] , sng-freeR)

        h : sngA ≤FR sngB 
        h = (here (⊑R₀-reflexive ha≈hb)) ∷ []

        p : (⊥L , |gR| sngB) ≈' (⊥L , (|gR| $ sngA ∨FR sngB)) 
        p = ( ≈L-refl , (|gR|-≈ sngB (sngA ∨FR sngB) $ ≈FR-sym {sngA ∨FR sngB} {sngB} (connecting→ {A = BoundedJoinSemilattice.joinSemiLattice FPR-BJS} sngA sngB h)) ) 
    |g|-∨ a@(ha ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@(hb ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l∥r ha∥hb with DeltaPoset.compare P ha hb
    |g|-∨ a@((inj₁ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@(hb ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l∥r ha∥hb | tri< ha<hb _ _ = 
      begin
        (|gL| sngA , ⊥R) ∨' (|g| $ (ta , fta) ∨F b) ≈⟨ ∨'-cong ≈'-refl (|g|-∨ (ta , fta) b) ⟩
        (|gL| sngA , ⊥R) ∨' ((|g| $ ta , fta) ∨' (|g| b)) ≈⟨ ≈'-sym (∨'-assoc (|gL| sngA , ⊥R) (|g| $ ta , fta) (|g| b)) ⟩
        ((|gL| sngA , ⊥R) ∨' (|g| $ ta , fta)) ∨' (|g| b) ≡⟨ PE.refl ⟩
        (|g| a) ∨' (|g| b)
       ∎
      where
        jsS = BoundedJoinSemilattice.joinSemiLattice S

        open import Relation.Binary.EqReasoning (≈'-setoid)      
        open import Relation.Binary.Properties.JoinSemilattice jsS
          renaming( ∨-assoc to ∨'-assoc ; ∨-comm to ∨'-comm ; ∨-cong to ∨'-cong )

        sngA : Carrier-FPL
        sngA = (ha ∷ [] , sng-freeL)
    |g|-∨ a@((inj₂ ha) ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@(hb ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l∥r ha∥hb | tri< ha<hb _ _ = 
      begin
        (⊥L , |gR| sngA) ∨' (|g| $ (ta , fta) ∨F b) ≈⟨ ∨'-cong ≈'-refl (|g|-∨ (ta , fta) b) ⟩
        (⊥L , |gR| sngA) ∨' ((|g| $ ta , fta) ∨' (|g| b)) ≈⟨ ≈'-sym (∨'-assoc (⊥L , |gR| sngA) (|g| $ ta , fta) (|g| b)) ⟩
        ((⊥L , |gR| sngA) ∨' (|g| $ ta , fta)) ∨' (|g| b) ≡⟨ PE.refl ⟩
        (|g| a) ∨' (|g| b)
       ∎
      where
        jsS = BoundedJoinSemilattice.joinSemiLattice S

        open import Relation.Binary.EqReasoning (≈'-setoid)      
        open import Relation.Binary.Properties.JoinSemilattice jsS
          renaming( ∨-assoc to ∨'-assoc ; ∨-comm to ∨'-comm ; ∨-cong to ∨'-cong )

        sngA : Carrier-FPR
        sngA = (ha ∷ [] , sng-freeR)
    |g|-∨ a@(ha ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@(hb ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l∥r ha∥hb | tri≈ _ ha≈hb _ = 
      ⊥-elim $ ha∥hb (inj₁ $ DeltaPoset.reflexive⊑ P ha≈hb)
    |g|-∨ a@(ha ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₁ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l∥r ha∥hb | tri> _ _ hb<ha = 
      begin
        (|gL| sngB , ⊥R) ∨' (|g| $ a ∨F (tb , ftb)) ≈⟨ ∨'-cong ≈'-refl (|g|-∨ a (tb , ftb)) ⟩
        (|gL| sngB , ⊥R) ∨' ((|g| a) ∨' (|g| $ tb , ftb)) ≈⟨ ≈'-sym (∨'-assoc (|gL| sngB , ⊥R) (|g| a) (|g| $ tb , ftb)) ⟩
        ((|gL| sngB , ⊥R) ∨' (|g| a)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-comm (|gL| sngB , ⊥R) (|g| a)) ≈'-refl ⟩
        ((|g| a) ∨' (|gL| sngB , ⊥R)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-assoc (|g| a) (|gL| sngB , ⊥R) (|g| $ tb , ftb) ⟩
        (|g| a) ∨' ((|gL| sngB , ⊥R) ∨' (|g| $ tb , ftb)) ≡⟨ PE.refl ⟩ 
        (|g| a) ∨' (|g| b)
       ∎
      where
        jsS = BoundedJoinSemilattice.joinSemiLattice S

        open import Relation.Binary.EqReasoning (≈'-setoid)      
        open import Relation.Binary.Properties.JoinSemilattice jsS
          renaming( ∨-assoc to ∨'-assoc ; ∨-comm to ∨'-comm ; ∨-cong to ∨'-cong )

        sngB : Carrier-FPL
        sngB = (hb ∷ [] , sng-freeL)
    |g|-∨ a@(ha ∷ ta , fa@(∷-Free _ _ _ _ fta)) b@((inj₂ hb) ∷ tb , fb@(∷-Free _ _ _ _ ftb)) | l∥r ha∥hb | tri> _ _ hb<ha = 
      begin
        (⊥L , |gR| sngB) ∨' (|g| $ a ∨F (tb , ftb)) ≈⟨ ∨'-cong ≈'-refl (|g|-∨ a (tb , ftb)) ⟩
        (⊥L , |gR| sngB) ∨' ((|g| a) ∨' (|g| $ tb , ftb)) ≈⟨ ≈'-sym (∨'-assoc (⊥L , |gR| sngB) (|g| a) (|g| $ tb , ftb)) ⟩
        ((⊥L , |gR| sngB) ∨' (|g| a)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-cong (∨'-comm (⊥L , |gR| sngB) (|g| a)) ≈'-refl ⟩
        ((|g| a) ∨' (⊥L , |gR| sngB)) ∨' (|g| $ tb , ftb) ≈⟨ ∨'-assoc (|g| a) (⊥L , |gR| sngB) (|g| $ tb , ftb) ⟩
        (|g| a) ∨' ((⊥L , |gR| sngB) ∨' (|g| $ tb , ftb)) ≡⟨ PE.refl ⟩ 
        (|g| a) ∨' (|g| b)
       ∎
      where
        jsS = BoundedJoinSemilattice.joinSemiLattice S

        open import Relation.Binary.EqReasoning (≈'-setoid)      
        open import Relation.Binary.Properties.JoinSemilattice jsS
          renaming( ∨-assoc to ∨'-assoc ; ∨-comm to ∨'-comm ; ∨-cong to ∨'-cong )

        sngB : Carrier-FPR
        sngB = (hb ∷ [] , sng-freeR)
    
⟦ IVarSemilat x ⁂⟧ = {!!}
⟦ PartialSemilat x ⁂⟧ = {!!}
