module SemKinding where

open import Util

open import Syntax
open import Kinding
open import BoolPoset

open import Level
open import FreeForgetfulAdjunction
open import Deltas

open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Lattice
open import Function.Inverse
open import Data.Product
open import Data.Empty
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Data.Nat as N renaming (_⊔_ to _⊔N_ ; _<_ to _<N_ ; _≤_ to _≤N_ ; _≤?_ to _≤N?_ ; _≟_ to _≟N?_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import SemScalars
open import PosetScalars
open import Preorders
--⁎⟧ ⁑⟧
----- Stoset conversion (for dealing with the eq field of SemStoset)
--[[[
conv : {P : Poset l0 l0 l0} → {T : StrictTotalOrder l0 l0 l0} → (eq : StrictTotalOrder.Eq.setoid T ≡ (poset→setoid P)) →
       (t : StrictTotalOrder.Eq.Carrier T) → Poset.Carrier P
conv {P} {T} PE.refl t = t

conv-≈ : {P : Poset l0 l0 l0} → {T : StrictTotalOrder l0 l0 l0} → (eq : StrictTotalOrder.Eq.setoid T ≡ (poset→setoid P)) →
         (t₁ t₂ : StrictTotalOrder.Eq.Carrier T) → (StrictTotalOrder.Eq._≈_ T t₁ t₂) → 
         (Poset._≈_ P (conv {P} {T} eq t₁) (conv {P} {T} eq t₂))
conv-≈ {P} {T} PE.refl t₁ t₂ t₁≈t₂ = t₁≈t₂

conv-inj : {P : Poset l0 l0 l0} → {T : StrictTotalOrder l0 l0 l0} → (eq : StrictTotalOrder.Eq.setoid T ≡ (poset→setoid P)) →
         (t₁ t₂ : StrictTotalOrder.Eq.Carrier T) → 
         (Poset._≈_ P (conv {P} {T} eq t₁) (conv {P} {T} eq t₂)) → 
         (StrictTotalOrder.Eq._≈_ T t₁ t₂)
conv-inj {P} {T} PE.refl t₁ t₂ t₁≈t₂ = t₁≈t₂
--]]]

-- Functions
--[[[
⇒-poset : (P : Preorder l0 l0 l0) → (Q : Poset l0 l0 l0) → Poset l0 l0 l0
--[[[
⇒-poset P Q =
  record
  { Carrier = P ⇒ Q'
  ; isPartialOrder = leqPartialOrder
  }
  where
    open import Relation.Binary.OrderMorphism renaming (_⇒-Poset_ to _⇛_)
    |P| : Set
    |P| = Preorder.Carrier P
    _d≈_ : |P| → |P| → Set
    _d≈_ = Preorder._≈_ P
    _d∼_ : |P| → |P| → Set
    _d∼_ = Preorder._∼_ P

    |Q| : Set
    |Q| = Poset.Carrier Q
    Q' = Poset.preorder Q
    _c≈_ : |Q| → |Q| → Set
    _c≈_ = Poset._≈_ Q
    _c≤_ : |Q| → |Q| → Set
    _c≤_ = Poset._≤_ Q
    isPartialOrderCod : IsPartialOrder _c≈_ _c≤_
    isPartialOrderCod = Poset.isPartialOrder Q

    _eq_ : (P ⇒ Q') → (P ⇒ Q') → Set
    f' eq g' = ∀ {v : |P|} → Poset._≈_ Q (f v) (g v)
      where
        f = _⇒_.fun f'
        g = _⇒_.fun g'

    _leq_ : (P ⇒ Q') → (P ⇒ Q') → Set
    f' leq g' = ∀{v : |P|} → (f v) c≤ (g v) 
      where
        f = _⇒_.fun f'
        g = _⇒_.fun g'

    eqRefl : Reflexive _eq_
    eqRefl {f} = Poset.Eq.refl Q

    eqSym : Symmetric _eq_
    eqSym {f} {g} f-eq-g = Poset.Eq.sym Q f-eq-g

    eqTrans : Transitive _eq_
    eqTrans {f} {g} {h} f-eq-g g-eq-h = Poset.Eq.trans Q f-eq-g g-eq-h 

    leqRefl : _eq_ Relation.Binary.⇒ _leq_
    leqRefl {f'} f-eq-f {v} = Poset.reflexive Q f-eq-f 
      where
        f = _⇒_.fun f'

    leqTransitive : Transitive _leq_
    leqTransitive {f'} {g'} {h'} f≤g g≤h {v} = trans≤ fv≤gv gv≤hv 
      where
        f = _⇒_.fun f'
        g = _⇒_.fun g'
        h = _⇒_.fun h'

        fv≤gv : (f v) c≤ (g v)
        fv≤gv = f≤g {v}

        gv≤hv : (g v) c≤ (h v)
        gv≤hv = g≤h {v}

        trans≤ : Transitive _c≤_
        trans≤ = IsPartialOrder.trans isPartialOrderCod

    leqAntisym : Antisymmetric _eq_ _leq_
    leqAntisym {f} {g} f≤g g≤f = Poset.antisym Q f≤g g≤f

    leqPartialOrder : IsPartialOrder _eq_ _leq_
    leqPartialOrder = record
      { isPreorder = record
         { isEquivalence = record
           { refl = λ {x} → eqRefl {x} 
           ; sym = λ {x} {y} → eqSym {x} {y} 
           ; trans = λ {x} {y} {z} → eqTrans {x} {y} {z} 
           }
         ; reflexive = λ {x} {y} → leqRefl {x} {y} 
         ; trans = λ {x} {y} {z} → leqTransitive {x} {y} {z} 
         }
      ;  antisym = λ {x} {y} → leqAntisym {x} {y}
      } 
--]]]

-- interpretation of poset kinding judgment
⟦_⋆⟧ : ∀ {τ : τ} → IsPoset τ → Poset l0 l0 l0

-- interpret as poset and then upcast to preorder
⟦_⋆⟧' : ∀ {τ : τ} → IsPoset τ → Preorder l0 l0 l0
⟦ wf ⋆⟧' = Poset.preorder ⟦ wf ⋆⟧

record SemStoset {τ : τ} (isStoset : IsStoset τ) : Set l1 where
  field
    T : StrictTotalOrder l0 l0 l0
    eq : StrictTotalOrder.Eq.setoid T ≡ (poset→setoid ⟦ stoset→poset isStoset ⋆⟧)

⟦_⋇⟧ : ∀ {τ : τ} → (p : IsStoset τ) → SemStoset p

record SemSemilatCore (cₛ ℓₛ₁ ℓₛ₂ cₚ ℓ⊑ₚ ℓ<ₚ ℓ~ₚ : Level) {τ τ₀ : τ} (isSemilat : IsSemilat τ τ₀)
                      : Set (Level.suc $ cₛ ⊔ ℓₛ₁ ⊔ ℓₛ₂ ⊔ cₚ ⊔ ℓ⊑ₚ ⊔ ℓ<ₚ ⊔ ℓ~ₚ) where
  field
    -- direct representation of semilattice
    S : BoundedJoinSemilattice l0 l0 l0
    US : (BoundedJoinSemilattice.poset S) ≡ ⟦ (semilat→poset isSemilat) ⋆⟧
    -- delta poset (freely generates S up-to-isomorphism)
    P : DeltaPoset {cₚ} {ℓ⊑ₚ} {ℓ<ₚ} {ℓ~ₚ}
    -- injection of τ₀ deltaPoset interpretation into P
    i : (DeltaPoset.preorder P) ↣+ ⟦ semilat→deltaPoset isSemilat ⋆⟧' 

-- partial interpretation of semilattice kinding judgment
-- this only includes the portion necessary for mutual recursion with poset kinding interpretation
-- the other portion is implemented in the SemilatKinding directory
⟦_Δ⟧ : ∀ {τ τ₀ : τ} → (isSemilat : IsSemilat τ τ₀) → SemSemilatCore l0 l0 l0 l0 l0 l0 l0 isSemilat   

⟦ FunPoset {q = q} domIsPoset codIsPoset ⋆⟧ = ⇒-poset (⟦ q q⟧ ⟦ domIsPoset ⋆⟧') ⟦ codIsPoset ⋆⟧
⟦ DictPoset domIsToset codIsSemilat ⋆⟧ = 
  ▹-poset (SemStoset.T ⟦ domIsToset ⋇⟧) (SemSemilatCore.S ⟦ codIsSemilat Δ⟧)
  where
    open import Dictionary
⟦ CapsulePoset q₀' isPosetContents ⋆⟧ = ⟦ q₀' q'⟧ ⟦ isPosetContents ⋆⟧ 
  where
    open import PosetScalars
⟦ ProductPoset isPosetL isPosetR ⋆⟧ = ×-poset ⟦ isPosetL ⋆⟧ ⟦ isPosetR ⋆⟧  
  where
    open import Data.Product
    open import Data.Product.Relation.Pointwise.NonDependent
⟦ SumPoset isPosetL isPosetR ⋆⟧ = ⊎-poset {l0} {l0} {l0} {l0} {l0} {l0} ⟦ isPosetL ⋆⟧ ⟦ isPosetR ⋆⟧  
  where
    open import Data.Sum
    open import Data.Sum.Relation.Pointwise
⟦ IVarPoset isStosetContents ⋆⟧ = ⌈⌉-poset (SemStoset.T ⟦ isStosetContents ⋇⟧)
  where
    open import IVar
⟦ PartialPoset isPosetContents ⋆⟧ = ⊎-<-poset {l0} {l0} {l0} {l0} {l0} {l0} ⟦ isPosetContents ⋆⟧ unitPoset 
  where
    open import Data.Sum.Relation.LeftOrder
    open import Data.Unit renaming (poset to unitPoset)
⟦ UnitPoset ⋆⟧ = poset
  where
    open import Data.Unit
⟦ BoolPoset ⋆⟧ = B≤-poset
  where
    open import BoolPoset
⟦ NatPoset ⋆⟧ = record 
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _≤_ = _≤_ 
  ; isPartialOrder = ≤-isPartialOrder
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties


⟦ UnitStoset ⋇⟧ = 
  record
  { T = UnitStrictTotal.⊤-strictTotalOrder
  ; eq = PE.refl
  }
⟦ NatStoset ⋇⟧ = 
  record
  { T = <-strictTotalOrder
  ; eq = PE.refl
  }
  where
    open import Data.Nat.Properties
⟦ BoolStoset ⋇⟧ = 
  record
  { T = B<-strictTotalOrder
  ; eq = PE.refl
  }
  where
    open import BoolPoset
⟦ ProductStoset stosetL stosetR ⋇⟧ =
  record
  { T = ×-strictTotalOrder (SemStoset.T ⟦ stosetL ⋇⟧) (SemStoset.T ⟦ stosetR ⋇⟧)
  ; eq = PE.cong₂ ×-setoid (SemStoset.eq ⟦ stosetL ⋇⟧) (SemStoset.eq ⟦ stosetR ⋇⟧)
  }
  where
    open import Data.Product.Relation.Pointwise.NonDependent using (×-setoid)
    open import Data.Product.Relation.Lex.Strict using (×-strictTotalOrder)
⟦ SumStoset stosetL stosetR ⋇⟧ = 
  record
  { T = ⊎-<-strictTotalOrder {l0} {l0} {l0} {l0} {l0} {l0} (SemStoset.T ⟦ stosetL ⋇⟧) (SemStoset.T ⟦ stosetR ⋇⟧)
  ; eq = PE.cong₂ ⊎-setoid (SemStoset.eq ⟦ stosetL ⋇⟧) (SemStoset.eq ⟦ stosetR ⋇⟧)
  }
  where
    open import Data.Sum.Relation.LeftOrder using (⊎-<-strictTotalOrder)
    open import Data.Sum.Relation.Pointwise using (⊎-setoid)
⟦ PartialStoset stosetContents ⋇⟧ =
  record
  { T = ⊎-<-strictTotalOrder {l0} {l0} {l0} {l0} {l0} {l0} (SemStoset.T ⟦ stosetContents ⋇⟧) ⊤-strictTotalOrder  
  ; eq = PE.cong₂ ⊎-setoid (SemStoset.eq ⟦ stosetContents ⋇⟧) PE.refl  
  } 
  where
    open import Data.Sum.Relation.LeftOrder
    open UnitStrictTotal using (⊤-strictTotalOrder)
    open import Data.Sum.Relation.Pointwise using (⊎-setoid)

⟦ BoolSemilat Δ⟧  =
  record
  { S = S
  ; US = PE.refl
  ; P = P
  ; i = |i| , |i|-monotone , |i|-monic
  }
  where
    open import Relation.Binary.Lattice
    open import Relation.Binary.PropositionalEquality as PE using (_≡_)
    open import Relation.Binary.Closure.ReflexiveTransitive
    open import UnitPoset
    open import Data.List
    open import Data.List.Any
    open import Data.List.Membership.Propositional renaming (_∈_ to _∈≡_)
    open import Data.Product
    open import Data.Unit
    open import Data.Empty
    open import Data.Sum
    open import Data.Bool

    open import Relation.Binary
    open import Deltas
    open import Level 
    open import Syntax
    open import Kinding
    open import Util
    open import FreeForgetfulAdjunction
    open import BoolPoset
    open import FinPoset     

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
    P = record
      { Carrier = ⊤ 
      ; _⊑_ = _⊑_ 
      ; _<_ = _<_
      ; isStrictTotalOrder = UnitStrictTotal.⊤-IsStrictTotalOrder
      ; isDecPartialOrder = ⊤≤-isDecPartialOrder
      ; convexity = convexity
      }
     where
       open import UnitPoset
       _⊑_ = _⊤≤_
       _<_ = UnitStrictTotal._⊤<_

       _∦_ : ⊤ → ⊤ → Set
       x ∦ y = x ⊤≤ y ⊎ y ⊤≤ x

       _∥_ : ⊤ → ⊤ → Set
       _∥_ x y = ¬ (x ∦ y)

       convexity : {a b c : ⊤} → a < b → b < c → a ∥ b → b ∥ c → a ∥ c
       convexity () () _ _


    |i| : (DeltaPoset.Carrier P) → (DeltaPoset.Carrier P)
    |i| tt = tt

    |i|-monotone : Monotone (DeltaPoset.preorder P) ⟦ semilat→deltaPoset BoolSemilat  ⋆⟧' |i|
    |i|-monotone {tt} {tt} tt⊑tt = record {}

    |i|-monic : Injective (DeltaPoset.≈-setoid P) (preorder→setoid ⟦ semilat→deltaPoset BoolSemilat ⋆⟧') |i|
    |i|-monic {tt} {tt} _ = PE.refl 

⟦ NatSemilat Δ⟧ = 
  record
  { S = S
  ; US = PE.refl
  ; P = P
  ; i = |i| , (λ {p} {p'} z → |i|-monotone {p} {p'} z) , (λ {a} {a'} z → |i|-monic {a} {a'} z)
  }
  where
   open import Data.Nat.Base as NB renaming (_⊔_ to _N⊔_)
   open import Data.Nat.Properties as NP
   open import Data.List.Any
   open import Data.List

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
   P = 
     record
      { Carrier = Σ[ n ∈ ℕ ] ¬ (n ≡ 0)
      ; _⊑_ = _⊑₀_
      ; _<_ = _<₀_
      ; _≈_ = _≈₀_
      ; isStrictTotalOrder = isStrictTotalOrder₀
      ; isDecPartialOrder = isDecPartialOrder₀
      ; convexity = λ {a} → λ {b} → λ {c} → convexity {a} {b} {c}
      }
      where
        open import Relation.Binary renaming (_⇒_ to _⇛_)
        open import Data.List
        open import Data.Nat.Properties

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

        convexity : {a b c : C} → (a <₀ b) → (b <₀ c) → (a ∥₀ b) → (b ∥₀ c) → (a ∥₀ c)
        convexity {a , _} {b , _} {c , _} _ _ a∥b b∥c = ⊥-elim $ a∥b (≤-total a b)

        <₀-compare : Trichotomous _≈₀_ _<₀_
        <₀-compare (a , _) (b , _) = <-cmp a b

        ⊑₀-reflexive : _≈₀_ ⇛ _⊑₀_
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

   |i| : (DeltaPoset.Carrier P) → (Poset.Carrier ⟦ semilat→deltaPoset NatSemilat ⋆⟧)
   |i| (n , p) = n

   |i|-monotone : Monotone (DeltaPoset.preorder P) ⟦ semilat→deltaPoset NatSemilat ⋆⟧' |i|
   |i|-monotone {n , _} {n' , _} n⊑n' = n⊑n'

   |i|-monic : Injective (DeltaPoset.≈-setoid P) (preorder→setoid ⟦ semilat→deltaPoset NatSemilat ⋆⟧') |i|
   |i|-monic {a , _} {a' , _} fa≈fa' = fa≈fa' 

   i : (DeltaPoset.preorder P) ↣+ ⟦ semilat→deltaPoset NatSemilat ⋆⟧'
   i = (|i| , (λ {a} → λ {a'} → |i|-monotone {a} {a'}) , (λ {a} → λ {a'} → |i|-monic {a} {a'}))

⟦ ProductSemilat isSemilatL isSemilatR Δ⟧ = record
  { S = S
  ; US = US
  ; P = P
  ; i = |i| , |i|-mono , |i|-injective
  }
  where
    open import Data.List.Relation.Pointwise as LPW hiding (Rel ; Pointwise)
    open import Data.Product.Relation.Pointwise.NonDependent as PW
    open import Data.Sum.Relation.Pointwise hiding (Pointwise)

    semSemilatL = ⟦ isSemilatL Δ⟧
    semSemilatR = ⟦ isSemilatR Δ⟧

    bjsL = SemSemilatCore.S semSemilatL
    bjsR = SemSemilatCore.S semSemilatR

    |L| = BoundedJoinSemilattice.Carrier bjsL
    |R| = BoundedJoinSemilattice.Carrier bjsR

    _≈L_ = BoundedJoinSemilattice._≈_ bjsL
    ≈L-refl = BoundedJoinSemilattice.Eq.refl bjsL
    ≈L-reflexive = BoundedJoinSemilattice.Eq.reflexive bjsL
    ≈L-sym = BoundedJoinSemilattice.Eq.sym bjsL
    ≈L-trans = BoundedJoinSemilattice.Eq.trans bjsL
    ≈L-setoid : Setoid _ _
    ≈L-setoid = record
      { Carrier = |L|
      ; isEquivalence = BoundedJoinSemilattice.isEquivalence bjsL
      }
    _≈R_ = BoundedJoinSemilattice._≈_ bjsR
    ≈R-refl = BoundedJoinSemilattice.Eq.refl bjsR
    ≈R-reflexive = BoundedJoinSemilattice.Eq.reflexive bjsR
    ≈R-sym = BoundedJoinSemilattice.Eq.sym bjsR
    ≈R-trans = BoundedJoinSemilattice.Eq.trans bjsR
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

    US : (BoundedJoinSemilattice.poset S) ≡ ⟦ (ProductPoset (semilat→poset isSemilatL) (semilat→poset isSemilatR)) ⋆⟧
    US = PE.cong₂ (λ x y → ×-poset x y) USL USR
      where
        USL : (BoundedJoinSemilattice.poset bjsL) ≡ ⟦ semilat→poset isSemilatL ⋆⟧
        USL = SemSemilatCore.US semSemilatL

        USR : (BoundedJoinSemilattice.poset bjsR) ≡ ⟦ semilat→poset isSemilatR ⋆⟧
        USR = SemSemilatCore.US semSemilatR

    joinSemilatticeS : JoinSemilattice l0 l0 l0
    joinSemilatticeS = BoundedJoinSemilattice.joinSemiLattice S

    ≈'-refl = BoundedJoinSemilattice.Eq.refl S
    ≈'-reflexive = BoundedJoinSemilattice.Eq.reflexive S
    ≈'-sym = BoundedJoinSemilattice.Eq.sym S

    ≈'-setoid : Setoid _ _
    ≈'-setoid = record
      { Carrier = Carrier'
      ; isEquivalence = ×-isEquivalence (BoundedJoinSemilattice.isEquivalence bjsL) (BoundedJoinSemilattice.isEquivalence bjsR)
      }

    deltaL = SemSemilatCore.P ⟦ isSemilatL Δ⟧
    deltaR = SemSemilatCore.P ⟦ isSemilatR Δ⟧

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
    convexL = DeltaPoset.convexity deltaL
    convexR = DeltaPoset.convexity deltaR

    P : DeltaPoset {l0} {l0} {l0} {l0}
    P = sumDeltaPoset
      where 
        open import Data.Sum.Relation.LeftOrder as LO
        open import Data.Sum.Relation.Pointwise as SPW

        CarrierL = DeltaPoset.Carrier deltaL
        CarrierR = DeltaPoset.Carrier deltaR
        _L<_ = DeltaPoset._<_ deltaL
        _R<_ = DeltaPoset._<_ deltaR
        _L⊑_ = DeltaPoset._⊑_ deltaL
        _R⊑_ = DeltaPoset._⊑_ deltaR
        _L∥_ = DeltaPoset._∥_ deltaL
        _R∥_ = DeltaPoset._∥_ deltaR
        _L∦_ = DeltaPoset._∦_ deltaL
        _R∦_ = DeltaPoset._∦_ deltaR
        _L≈_ =  DeltaPoset._≈_ deltaL
        _R≈_ =  DeltaPoset._≈_ deltaR

        |P| = CarrierL ⊎ CarrierR
        _<ₚ_ = _L<_ ⊎-< _R<_
        _⊑ₚ_ = SPW.Pointwise _L⊑_ _R⊑_
        _≈ₚ_ = SPW.Pointwise _L≈_ _R≈_

        _∦ₚ_ : |P| → |P| → Set _
        a ∦ₚ b = (a ⊑ₚ b) ⊎ (b ⊑ₚ a)  

        _∥ₚ_ : |P| → |P| → Set _
        a ∥ₚ b = ¬ (a ∦ₚ b)

        tosetLR : IsStrictTotalOrder _≈ₚ_ _<ₚ_ 
        tosetLR = ⊎-<-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder deltaL) (DeltaPoset.isStrictTotalOrder deltaR)

        partialOrderLR : IsPartialOrder _≈ₚ_ _⊑ₚ_
        partialOrderLR = ⊎-isPartialOrder (DeltaPoset.isPartialOrder deltaL) (DeltaPoset.isPartialOrder deltaR)

        ≈ₚ-equiv : IsEquivalence _≈ₚ_
        ≈ₚ-equiv = IsPartialOrder.isEquivalence partialOrderLR

        ≈ₚ-setoid : Setoid _ _
        ≈ₚ-setoid = record
          { Carrier = |P|
          ; isEquivalence = ≈ₚ-equiv
          }

        convexity : {a b c : |P|} → a <ₚ b → b <ₚ c → a ∥ₚ b → b ∥ₚ c → a ∥ₚ c
        convexity {inj₁ a'} {inj₂ b'} {inj₁ c'} (₁∼₂ .tt) () a∥b b∥c a∦c
        convexity {inj₁ a'} {inj₂ b'} {inj₂ c'} (₁∼₂ .tt) (₂∼₂ b'<c') a∥b b∥c (inj₁ (₁∼₂ ()))
        convexity {inj₁ a'} {inj₂ b'} {inj₂ c'} (₁∼₂ .tt) (₂∼₂ b'<c') a∥b b∥c (inj₂ ())
        convexity {inj₁ a'} {inj₁ b'} {inj₂ c'} (₁∼₁ a'<b') (₁∼₂ .tt) a∥b b∥c (inj₁ (₁∼₂ ()))
        convexity {inj₁ a'} {inj₁ b'} {inj₂ c'} (₁∼₁ a'<b') (₁∼₂ .tt) a∥b b∥c (inj₂ ())
        convexity {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c a∦c with a'∥b' | b'∥c'
          where
            a'∥b' : a' L∥ b'
            a'∥b' (inj₁ a'⊑b') = a∥b $ inj₁ (₁∼₁ a'⊑b')
            a'∥b' (inj₂ b'⊑a') = a∥b $ inj₂ (₁∼₁ b'⊑a')

            b'∥c' : b' L∥ c'
            b'∥c' (inj₁ b'⊑c') = b∥c $ inj₁ (₁∼₁ b'⊑c')
            b'∥c' (inj₂ c'⊑b') = b∥c $ inj₂ (₁∼₁ c'⊑b')
        convexity {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c (inj₁ (₁∼₁ a'⊑c')) | a'∥b' | b'∥c' =
          (convexL a'<b' b'<c' a'∥b' b'∥c') (inj₁ a'⊑c')
        convexity {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c (inj₂ (₁∼₁ c'⊑a')) | a'∥b' | b'∥c' =
          (convexL a'<b' b'<c' a'∥b' b'∥c') (inj₂ c'⊑a')
        convexity {inj₂ a'} {inj₂ b'} {inj₂ c'} (₂∼₂ a'<b') (₂∼₂ b'<c') a∥b b∥c a∦c with a'∥b' | b'∥c'
          where
            a'∥b' : a' R∥ b'
            a'∥b' (inj₁ a'⊑b') = a∥b $ inj₁ (₂∼₂ a'⊑b')
            a'∥b' (inj₂ b'⊑a') = a∥b $ inj₂ (₂∼₂ b'⊑a')

            b'∥c' : b' R∥ c'
            b'∥c' (inj₁ b'⊑c') = b∥c $ inj₁ (₂∼₂ b'⊑c')
            b'∥c' (inj₂ c'⊑b') = b∥c $ inj₂ (₂∼₂ c'⊑b')
        convexity {inj₂ a'} {inj₂ b'} {inj₂ c'} (₂∼₂ a'<b') (₂∼₂ b'<c') a∥b b∥c (inj₁ (₂∼₂ a'⊑c')) | a'∥b' | b'∥c' =
          (convexR a'<b' b'<c' a'∥b' b'∥c') (inj₁ a'⊑c')
        convexity {inj₂ a'} {inj₂ b'} {inj₂ c'} (₂∼₂ a'<b') (₂∼₂ b'<c') a∥b b∥c (inj₂ (₂∼₂ c'⊑a')) | a'∥b' | b'∥c' =
          (convexR a'<b' b'<c' a'∥b' b'∥c') (inj₂ c'⊑a')

        sumDeltaPoset : DeltaPoset {_} {_} {_} {_}
        sumDeltaPoset = record  
          { Carrier = |P|
          ; _⊑_ = _⊑ₚ_
          ; _<_ = _<ₚ_
          ; isStrictTotalOrder = tosetLR
          ; isDecPartialOrder = record
            { isPartialOrder = partialOrderLR
            ; _≟_ = ⊎-decidable (DeltaPoset._≈?_ deltaL) (DeltaPoset._≈?_ deltaR) 
            ; _≤?_ = ⊎-decidable (DeltaPoset._⊑?_ deltaL) (DeltaPoset._⊑?_ deltaR) 
            }
          ; convexity = convexity
          }

    |P| : Set
    |P| = DeltaPoset.Carrier P

    _≈P_ : |P| → |P| → Set
    _≈P_ = DeltaPoset._≈_ P

    ≈P-setoid : Setoid _ _
    ≈P-setoid = DeltaPoset.≈-setoid P
    ≈P-reflexive = DeltaPoset.Eq.reflexive P
    ≈P-refl = DeltaPoset.Eq.refl P
    ≈P-trans = DeltaPoset.Eq.trans P
    ≈P-sym = DeltaPoset.Eq.sym P

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

    iL : (DeltaPoset.preorder deltaL) ↣+ ⟦ semilat→deltaPoset isSemilatL ⋆⟧'   
    iL = SemSemilatCore.i semSemilatL

    |iL| : (DeltaPoset.Carrier deltaL) → Preorder.Carrier ⟦ semilat→deltaPoset isSemilatL ⋆⟧'
    |iL| = proj₁ iL

    iL-mono : Monotone (DeltaPoset.preorder deltaL) ⟦ semilat→deltaPoset isSemilatL ⋆⟧' |iL|
    iL-mono = proj₁ $ proj₂ iL

    iL-injective : 
      Injective 
      (DeltaPoset.≈-setoid deltaL) 
      (preorder→setoid ⟦ semilat→deltaPoset isSemilatL ⋆⟧') 
      |iL|
    iL-injective = proj₂ $ proj₂ iL

    iR : (DeltaPoset.preorder deltaR) ↣+ ⟦ semilat→deltaPoset isSemilatR ⋆⟧' 
    iR = SemSemilatCore.i semSemilatR

    |iR| : DeltaPoset.Carrier deltaR → Preorder.Carrier ⟦ semilat→deltaPoset isSemilatR ⋆⟧' 
    |iR| = let |iR| , _ , _ = iR in |iR|

    iR-mono : Monotone (DeltaPoset.preorder deltaR) ⟦ semilat→deltaPoset isSemilatR ⋆⟧' |iR|
    iR-mono = let _ , iR-mono , _ = iR in iR-mono

    iR-injective : Injective (DeltaPoset.≈-setoid deltaR) (preorder→setoid ⟦ semilat→deltaPoset isSemilatR ⋆⟧') |iR|
    iR-injective = let _ , _ , iR-injective = iR in iR-injective

    |i| : DeltaPoset.Carrier P → Preorder.Carrier ⟦ semilat→deltaPoset $ ProductSemilat isSemilatL isSemilatR ⋆⟧' 
    |i| (inj₁ x) = inj₁ (|iL| x) 
    |i| (inj₂ x) = inj₂ (|iR| x)

    |i|-mono : Monotone (DeltaPoset.preorder P) ⟦ semilat→deltaPoset $ ProductSemilat isSemilatL isSemilatR ⋆⟧' |i|
    |i|-mono {inj₁ a'} {inj₁ b'} (₁∼₁ a'⊑b') = ₁∼₁ (iL-mono a'⊑b')
    |i|-mono {inj₁ a'} {inj₂ b'} (₁∼₂ ())
    |i|-mono {inj₂ a'} {inj₁ x} ()
    |i|-mono {inj₂ a'} {inj₂ b'} (₂∼₂ a'⊑b') = ₂∼₂ (iR-mono a'⊑b')

    |i|-injective : Injective (DeltaPoset.≈-setoid P) (preorder→setoid ⟦ semilat→deltaPoset $ ProductSemilat isSemilatL isSemilatR ⋆⟧') |i|
    |i|-injective {inj₁ a'} {inj₁ b'} (₁∼₁ ia'≈ib') = ₁∼₁ (iL-injective ia'≈ib')
    |i|-injective {inj₁ a'} {inj₂ b'} (₁∼₂ ())
    |i|-injective {inj₂ a'} {inj₁ b'} ()
    |i|-injective {inj₂ a'} {inj₂ b'} (₂∼₂ ia'≈ib') = ₂∼₂ (iR-injective ia'≈ib')

⟦ PartialSemilat isContentsSemilat Δ⟧ = 
  record 
  { S = S
  ; US = US
  ; P = P
  ; i = |i| , |i|-monotone , |i|-injective
  }
  where
    open import Data.Unit renaming (setoid to unitSetoid ; poset to unitPoset)
    open import Data.Sum.Relation.LeftOrder
    open import Data.Sum.Relation.Pointwise using (⊎-setoid)
    open import Data.Sum

    semContents : SemSemilatCore l0 l0 l0 l0 l0 l0 l0 isContentsSemilat
    semContents = ⟦ isContentsSemilat Δ⟧ 

    deltaContents : DeltaPoset {l0} {l0} {l0} {l0}
    deltaContents = SemSemilatCore.P semContents

    bjsContents : BoundedJoinSemilattice l0 l0 l0
    bjsContents = SemSemilatCore.S semContents

    S : BoundedJoinSemilattice l0 l0 l0
    S = record
      { Carrier = Carrier
      ; _≈_ = SPW.Pointwise (BoundedJoinSemilattice._≈_ bjsContents) _≡_
      ; _≤_ = _≤ᵀ_
      ; _∨_ = _∨ᵀ_ 
      ; ⊥ = ⊥ᵀ
      ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
          { isPartialOrder = ⊎-<-isPartialOrder (BoundedJoinSemilattice.isPartialOrder bjsContents) 
                                                (Poset.isPartialOrder unitPoset)
          ; supremum = supremum
          }
          ; minimum = minimum
        }
      }
      where
        open UnitStrictTotal using (⊤-strictTotalOrder)
        open import Data.Sum.Relation.Pointwise as SPW using (⊎-setoid)
        Carrier = (BoundedJoinSemilattice.Carrier bjsContents) ⊎ ⊤
        module isBjsContents = IsBoundedJoinSemilattice (BoundedJoinSemilattice.isBoundedJoinSemilattice bjsContents)

        _≤ᵀ_ = (BoundedJoinSemilattice._≤_ bjsContents) ⊎-< (Poset._≤_ unitPoset)
        ⊥ᵀ = inj₁ (BoundedJoinSemilattice.⊥ bjsContents)
        _∨'_ = BoundedJoinSemilattice._∨_ bjsContents

        _∨ᵀ_ : Carrier → Carrier → Carrier 
        inj₁ a ∨ᵀ inj₁ b = inj₁ (a ∨' b)
        inj₁ _ ∨ᵀ inj₂ tt = inj₂ tt
        inj₂ tt ∨ᵀ inj₁ _ = inj₂ tt
        inj₂ tt ∨ᵀ inj₂ tt = inj₂ tt

        upper : (x y : Carrier) → x ≤ᵀ (x ∨ᵀ y) × y ≤ᵀ (x ∨ᵀ y)
        upper (inj₁ x) (inj₁ y) = ₁∼₁ (proj₁ $ isBjsContents.supremum x y) , ₁∼₁ (proj₁ $ proj₂ $ isBjsContents.supremum x y)
        upper (inj₁ x) (inj₂ tt) = ₁∼₂ tt , ₂∼₂ (record {})
        upper (inj₂ tt) (inj₁ x) = ₂∼₂ (record {}) , ₁∼₂ tt
        upper (inj₂ tt) (inj₂ tt) = ₂∼₂ (record {}) , ₂∼₂ (record {})

        least : (x y : Carrier) → (z : Carrier) → (x ≤ᵀ z) → (y ≤ᵀ z) → ((x ∨ᵀ y) ≤ᵀ z)
        least .(inj₁ _) .(inj₁ _) .(inj₂ tt) (₁∼₂ tt) (₁∼₂ tt) = ₁∼₂ tt
        least .(inj₁ _) .(inj₂ _) .(inj₂ _) (₁∼₂ tt) (₂∼₂ (record {})) = ₂∼₂ (record {})
        least (inj₁ x) (inj₁ y) (inj₁ z) (₁∼₁ x≤z) (₁∼₁ y≤z) = ₁∼₁ $ (proj₂ $ proj₂ $ isBjsContents.supremum x y) z x≤z y≤z
        least .(inj₂ _) .(inj₁ _) .(inj₂ _) (₂∼₂ (record {})) (₁∼₂ tt) = ₂∼₂ (record {})
        least .(inj₂ _) .(inj₂ _) .(inj₂ _) (₂∼₂ (record {})) (₂∼₂ (record{})) = ₂∼₂ (record {})

        supremum : Supremum _≤ᵀ_ _∨ᵀ_
        supremum x y = ( (proj₁ $ upper x y) , (proj₂ $ upper x y) , (least x y) )

        minimum : Minimum _≤ᵀ_ ⊥ᵀ 
        minimum (inj₁ x) = ₁∼₁ (isBjsContents.minimum x)
        minimum (inj₂ tt) = ₁∼₂ tt

    US : (BoundedJoinSemilattice.poset S) ≡ ⟦ semilat→poset (PartialSemilat isContentsSemilat) ⋆⟧
    US = PE.cong₂ (⊎-<-poset {l0} {l0} {l0} {l0} {l0} {l0}) (SemSemilatCore.US semContents) PE.refl

    P : DeltaPoset {l0} {l0} {l0} {l0}
    P = record
      { Carrier = Carrier₀
      ; _⊑_ = _≤₀_
      ; _<_ = _<₀_
      ; _≈_ = _≈₀_
      ; isStrictTotalOrder = ⊎-<-isStrictTotalOrder (DeltaPoset.isStrictTotalOrder P') (UnitStrictTotal.⊤-IsStrictTotalOrder)
      ; isDecPartialOrder = record
        { isPartialOrder = ⊎-<-isPartialOrder (IsDecPartialOrder.isPartialOrder isDecPartialOrder₀) 
                                               (Poset.isPartialOrder unitPoset)
        ; _≟_ = _≟₀_
        ; _≤?_ = _≤₀?_
        } 
      ; convexity = convexity
      } 
      where
        open import Data.Sum.Relation.Pointwise as SPW using (⊎-setoid)
        open import Data.Sum.Relation.LeftOrder
        open import Data.Unit renaming (poset to unitPoset ; setoid to unitSetoid)

        P' : DeltaPoset {l0} {l0} {l0} {l0}
        P' = deltaContents 

        isDecPartialOrder₀ : IsDecPartialOrder (DeltaPoset._≈_ P') (DeltaPoset._⊑_ P')
        isDecPartialOrder₀ = DeltaPoset.isDecPartialOrder P'

        Carrier₀ : Set
        Carrier₀ = (DeltaPoset.Carrier P') ⊎ ⊤

        _≈₀_ : Carrier₀ → Carrier₀ → Set
        _≈₀_ = SPW.Pointwise (DeltaPoset._≈_ P') _≡_

        _≟₀_ : Decidable _≈₀_
        inj₁ a ≟₀ inj₁ b with IsDecPartialOrder._≟_ isDecPartialOrder₀ a b 
        inj₁ a ≟₀ inj₁ b | yes a≈b = yes $ ₁∼₁ a≈b 
        inj₁ a ≟₀ inj₁ b | no ¬a≈b = no ¬inj₁a≈₀inj₁b
          where
            ¬inj₁a≈₀inj₁b : ¬ (inj₁ a ≈₀ inj₁ b)
            ¬inj₁a≈₀inj₁b (₁∼₁ a≈b) = ¬a≈b a≈b
        inj₁ a ≟₀ inj₂ tt = no ¬inj₁a≈₀inj₂tt
          where
            ¬inj₁a≈₀inj₂tt : ¬ (inj₁ a ≈₀ inj₂ tt)
            ¬inj₁a≈₀inj₂tt (₁∼₂ ())
        inj₂ tt ≟₀ inj₁ b = no (λ ())
        inj₂ tt ≟₀ inj₂ tt = yes (₂∼₂ PE.refl)

        _≤₀_ : Carrier₀ → Carrier₀ → Set
        _≤₀_ = (DeltaPoset._⊑_ P') ⊎-< (Poset._≤_ unitPoset)

        _≤₀?_ : Decidable _≤₀_
        inj₁ a ≤₀? inj₁ b with IsDecPartialOrder._≤?_ isDecPartialOrder₀ a b
        inj₁ a ≤₀? inj₁ b | yes a≤b = yes $ ₁∼₁ a≤b
        inj₁ a ≤₀? inj₁ b | no ¬a≤b = no $ ¬inj₁a≤₀inj₁b
          where
            ¬inj₁a≤₀inj₁b : ¬ (inj₁ a ≤₀ inj₁ b)
            ¬inj₁a≤₀inj₁b (₁∼₁ a≤b) = ¬a≤b a≤b
        inj₁ a ≤₀? inj₂ tt = yes (₁∼₂ tt)
        inj₂ tt ≤₀? inj₁ b = no (λ ())
        inj₂ tt ≤₀? inj₂ tt = yes (₂∼₂ (record {}))

        _<₀_ : Carrier₀ → Carrier₀ → Set
        _<₀_ = (DeltaPoset._<_ P') ⊎-< (UnitStrictTotal._⊤<_)

        _∦₀_ : Carrier₀ → Carrier₀ → Set
        a ∦₀ b = (a ≤₀ b) ⊎ (b ≤₀ a) 

        _∥₀_ : Carrier₀ → Carrier₀ → Set
        a ∥₀ b = ¬ (a ∦₀ b)

        _∥_ = DeltaPoset._∥_ P'
        _∦_ = DeltaPoset._∦_ P'
        _⊑_ = DeltaPoset._⊑_ P'

        convexity : {a b c : Carrier₀} → (a <₀ b) → (b <₀ c) → (a ∥₀ b) → (b ∥₀ c) → (a ∥₀ c)
        convexity {inj₁ a'} {inj₁ b'} {inj₁ c'} (₁∼₁ a'<b') (₁∼₁ b'<c') a∥b b∥c = a∥c
          where
            a'∥b' : a' ∥ b'
            a'∥b' (inj₁ a'⊑b') = a∥b (inj₁ $ ₁∼₁ a'⊑b')
            a'∥b' (inj₂ b'⊑a') = a∥b (inj₂ $ ₁∼₁ b'⊑a')

            b'∥c' : b' ∥ c'
            b'∥c' (inj₁ b'⊑c') = b∥c (inj₁ $ ₁∼₁ b'⊑c')
            b'∥c' (inj₂ c'⊑b') = b∥c (inj₂ $ ₁∼₁ c'⊑b')

            a'∥c' : a' ∥ c'
            a'∥c' = (DeltaPoset.convexity P') a'<b' b'<c' a'∥b' b'∥c' 

            a∥c : (inj₁ a') ∥₀ (inj₁ c')
            a∥c (inj₁ (₁∼₁ a'⊑c')) = a'∥c' (inj₁ a'⊑c')
            a∥c (inj₂ (₁∼₁ c'⊑a')) = a'∥c' (inj₂ c'⊑a')
        convexity {inj₁ a'} {inj₁ b'} {inj₂ tt} (₁∼₁ a'⊑b') (₁∼₂ tt) a∥b b∥c = ⊥-elim $ b∥c (inj₁ (₁∼₂ tt))
        convexity {inj₁ x} {inj₂ y} {c} a<b b<c a∥b b∥c = ⊥-elim $ a∥b (inj₁ (₁∼₂ tt))
        convexity {inj₂ y} {inj₁ x} {c} () b<c a∥b b∥c
        convexity {inj₂ y} {inj₂ y₁} {c} (₂∼₂ ()) b<c a∥b b∥c

    |i| : (DeltaPoset.Carrier P) →
          (Poset.Carrier ⟦ PartialPoset (semilat→deltaPoset isContentsSemilat) ⋆⟧) 
    |i| (inj₁ x) = inj₁ $ (proj₁ $ SemSemilatCore.i semContents) x 
    |i| (inj₂ x) = inj₂ x

    |i|-monotone :
      Monotone 
        (DeltaPoset.preorder P)
        (Poset.preorder ⟦ PartialPoset (semilat→deltaPoset isContentsSemilat) ⋆⟧)
        |i|
    |i|-monotone {inj₁ a'} {inj₁ b'} (₁∼₁ a'∼b') = ₁∼₁ $ (proj₁ $ proj₂ $ SemSemilatCore.i semContents) a'∼b'
    |i|-monotone {inj₁ x} {inj₂ tt} (₁∼₂ tt) = ₁∼₂ tt
    |i|-monotone {inj₂ tt} {inj₁ x} ()
    |i|-monotone {inj₂ tt} {inj₂ tt} (₂∼₂ (record {})) = ₂∼₂ (record {})

    |i|-injective : 
      Injective 
        (preorder→setoid $ DeltaPoset.preorder P)
        (preorder→setoid $ Poset.preorder ⟦ PartialPoset (semilat→deltaPoset isContentsSemilat) ⋆⟧) |i|
    |i|-injective {inj₁ a'} {inj₁ b'} (₁∼₁ ia'≈ib') = ₁∼₁ $ (proj₂ $ proj₂ $ SemSemilatCore.i semContents) ia'≈ib'
    |i|-injective {inj₁ a'} {inj₂ b'} (₁∼₂ ())
    |i|-injective {inj₂ a'} {inj₁ b'} ()
    |i|-injective {inj₂ a'} {inj₂ b'} (₂∼₂ PE.refl) = ₂∼₂ PE.refl

⟦ IVarSemilat isContentStoset Δ⟧ = record
  { S = ⌈⌉-semilat
  ; P = deltaPoset
  ; US = PE.refl
  ; i = |i| , |i|-monotone , |i|-injective
  }
  where
    T = SemStoset.T ⟦ isContentStoset ⋇⟧
    open import IVar T
    open import DiscreteDelta T using (sym≈ ; deltaPoset ; ⊑-refl)
    P = deltaPoset
    |P| = DeltaPoset.Carrier P
    eq = SemStoset.eq ⟦ isContentStoset ⋇⟧

    |i| : |P| → Poset.Carrier ⟦ semilat→deltaPoset (IVarSemilat isContentStoset)  ⋆⟧
    |i| p = conv {⟦ stoset→poset isContentStoset ⋆⟧} {SemStoset.T ⟦ isContentStoset ⋇⟧} eq p
    
    |i|-monotone : Monotone (DeltaPoset.preorder P) ⟦ semilat→deltaPoset (IVarSemilat isContentStoset) ⋆⟧' |i|
    |i|-monotone {p} {p'} (⊑-refl p≈p') = 
      (reflexive (conv-≈ eq p p' p≈p') , reflexive (conv-≈ eq p' p (sym≈ p≈p')))  
      where
        open Preorder ⟦ stoset→poset isContentStoset ⋆⟧' using (reflexive)

    |i|-injective : 
      Injective 
        (preorder→setoid $ DeltaPoset.preorder P)
        (preorder→setoid ⟦ semilat→deltaPoset $ IVarSemilat isContentStoset ⋆⟧') 
        |i|
    |i|-injective {p} {p'} |i|p≈|i|p' = conv-inj eq p p' |i|p≈|i|p'

⟦ DictSemilat isDomStoset isCodSemilat Δ⟧ = record
  { S = ▹-semilat (SemStoset.T ⟦ isDomStoset ⋇⟧) (SemSemilatCore.S ⟦ isCodSemilat Δ⟧)
  ; P = P
  ; US = PE.refl
  ; i = |i| , |i|-monotone , |i|-injective 
  }
  where
    open import Dictionary
    open import Data.Product.Relation.Pointwise.NonDependent as PW
    open import Data.Product.Relation.Lex.Strict as LS

    T₀ : StrictTotalOrder l0 l0 l0
    T₀ = SemStoset.T ⟦ isDomStoset ⋇⟧

    P₀ : DeltaPoset {l0} {l0} {l0} {l0}
    P₀ = SemSemilatCore.P ⟦ isCodSemilat Δ⟧ 

    _≈T₀_ = StrictTotalOrder._≈_ T₀
    _<T₀_ = StrictTotalOrder._<_ T₀
    _⊑P₀_ = DeltaPoset._⊑_ P₀
    _<P₀_ = DeltaPoset._<_ P₀
    _∦P₀_ = DeltaPoset._∦_ P₀
    _∥P₀_ = DeltaPoset._∥_ P₀

    |P| = (StrictTotalOrder.Carrier T₀) × (DeltaPoset.Carrier P₀)
    _≈'_ = PW.Pointwise (StrictTotalOrder._≈_ T₀) (DeltaPoset._≈_ P₀)
    _<'_ = LS.×-Lex (StrictTotalOrder._≈_ T₀) (StrictTotalOrder._<_ T₀) (DeltaPoset._<_ P₀)
    _⊑'_ = PW.Pointwise (StrictTotalOrder._≈_ T₀) (DeltaPoset._⊑_ P₀)

    _∦'_ : |P| → |P| → Set
    p₁ ∦' p₂ = (p₁ ⊑' p₂) ⊎ (p₂ ⊑' p₁) 

    _∥'_ : |P| → |P| → Set
    p₁ ∥' p₂ = ¬ (p₁ ∦' p₂) 

    P : DeltaPoset {l0} {l0} {l0} {l0}
    --[[[
    P = record
      { Carrier = |P|
      ; _≈_ = _≈'_
      ; _<_ = _<'_
      ; _⊑_ = _⊑'_
      ; isStrictTotalOrder = LS.×-isStrictTotalOrder (StrictTotalOrder.isStrictTotalOrder T₀) (DeltaPoset.isStrictTotalOrder P₀)
      ; isDecPartialOrder = record
        { isPartialOrder = PW.×-isPartialOrder ≈discrete-isPartial ⊑-isPartial 
        ; _≤?_ = PW.×-decidable (StrictTotalOrder._≟_ T₀) (IsDecPartialOrder._≤?_ $ DeltaPoset.isDecPartialOrder P₀)
        ; _≟_ = PW.×-decidable (StrictTotalOrder._≟_ T₀) (IsStrictTotalOrder._≟_ $ DeltaPoset.isStrictTotalOrder P₀) 
        }
      ; convexity = convexity
      }
      where
        ⊑-isPartial : IsPartialOrder (DeltaPoset._≈_ P₀) (DeltaPoset._⊑_ P₀)
        ⊑-isPartial = IsDecPartialOrder.isPartialOrder (DeltaPoset.isDecPartialOrder P₀)

        ≈discrete-isPartial : IsPartialOrder (StrictTotalOrder._≈_ T₀) (StrictTotalOrder._≈_ T₀)
        ≈discrete-isPartial = record
          { isPreorder = record
            { isEquivalence = StrictTotalOrder.isEquivalence T₀
            ; reflexive = λ x≈y → x≈y 
            ; trans = IsEquivalence.trans $ StrictTotalOrder.isEquivalence T₀ 
            }
          ; antisym = λ {x} {y} x≈y y≈x → x≈y
          }
        
        convexity : {a b c : |P|} → a <' b → b <' c → a ∥' b → b ∥' c → a ∥' c
        --[[[
        convexity {a@(al , ar)} {b@(bl , br)} {c@(cl , cr)} (inj₁ al<bl) (inj₁ bl<cl) a∥b b∥c = 
          a∥c
          where
            al<cl : al <T₀ cl
            al<cl = StrictTotalOrder.trans T₀ al<bl bl<cl

            a∥c : a ∥' c
            a∥c (inj₁ (al≈cl , ar⊑cr)) = StrictTotalOrder.irrefl T₀ al≈cl al<cl   
            a∥c (inj₂ (cl≈al , cr⊑ar)) = StrictTotalOrder.irrefl T₀ (StrictTotalOrder.Eq.sym T₀ cl≈al) al<cl
        convexity {a@(al , ar)} {b@(bl , br)} {c@(cl , cr)} (inj₁ al<bl) (inj₂ (bl≈cl , br<cr)) a∥b b∥c = 
          a∥c
          where
            al<cl : al <T₀ cl
            al<cl = StrictTotalOrder.<-respʳ-≈  T₀ bl≈cl al<bl

            a∥c : a ∥' c
            a∥c (inj₁ (al≈cl , ar⊑cr)) = StrictTotalOrder.irrefl T₀ al≈cl al<cl   
            a∥c (inj₂ (cl≈al , cr⊑ar)) = StrictTotalOrder.irrefl T₀ (StrictTotalOrder.Eq.sym T₀ cl≈al) al<cl
        convexity {a@(al , ar)} {b@(bl , br)} {c@(cl , cr)} (inj₂ (al≈bl , ar<br)) (inj₁ bl<cl) a∥b b∥c = 
          a∥c
          where
            al<cl : al <T₀ cl
            al<cl = StrictTotalOrder.<-respˡ-≈  T₀ (StrictTotalOrder.Eq.sym T₀ al≈bl) bl<cl

            a∥c : a ∥' c
            a∥c (inj₁ (al≈cl , ar⊑cr)) = StrictTotalOrder.irrefl T₀ al≈cl al<cl   
            a∥c (inj₂ (cl≈al , cr⊑ar)) = StrictTotalOrder.irrefl T₀ (StrictTotalOrder.Eq.sym T₀ cl≈al) al<cl
        convexity {a@(al , ar)} {b@(bl , br)} {c@(cl , cr)} (inj₂ (al≈bl , ar<br)) (inj₂ (bl≈cl , br<cr)) a∥b b∥c = 
          a∥c
          where
            ar∥br : ar ∥P₀ br
            ar∥br (inj₁ ar⊑br) = a∥b $ inj₁ (al≈bl , ar⊑br)
            ar∥br (inj₂ br⊑ar) = a∥b $ inj₂ (StrictTotalOrder.Eq.sym T₀ al≈bl , br⊑ar)

            br∥cr : br ∥P₀ cr
            br∥cr (inj₁ br⊑cr) = b∥c $ inj₁ (bl≈cl , br⊑cr)
            br∥cr (inj₂ cr⊑br) = b∥c $ inj₂ (StrictTotalOrder.Eq.sym T₀ bl≈cl , cr⊑br)

            ar∥cr : ar ∥P₀ cr            
            ar∥cr = DeltaPoset.convexity P₀ ar<br br<cr ar∥br br∥cr
 
            a∥c : a ∥' c
            a∥c (inj₁ (al≈cl , ar⊑cr)) = ar∥cr $ inj₁ ar⊑cr
            a∥c (inj₂ (cl≈al , cr⊑ar)) = ar∥cr $ inj₂ cr⊑ar 
        --]]]
    --]]]

    eq = SemStoset.eq ⟦ isDomStoset ⋇⟧

    |i| : (DeltaPoset.Carrier P) → (Poset.Carrier ⟦ semilat→deltaPoset $ DictSemilat isDomStoset isCodSemilat ⋆⟧)
    |i| (t , s) = 
      (conv {P = ⟦ stoset→poset isDomStoset ⋆⟧} {T = T₀} eq t) , ((proj₁ $ SemSemilatCore.i ⟦ isCodSemilat Δ⟧) s)

    |i|-monotone : 
      Monotone
        (DeltaPoset.preorder P) 
        ⟦ ProductPoset (CapsulePoset qAny' $ stoset→poset isDomStoset) (semilat→deltaPoset isCodSemilat) ⋆⟧'
        |i|
    --[[[
    |i|-monotone {t , s} {t' , s'} (t≈t' , s≤s') = 
      ((ct≤ct' , ct'≤ct) , (proj₁ $ proj₂ $ SemSemilatCore.i ⟦ isCodSemilat Δ⟧) s≤s') 
      where
        Q : Poset l0 l0 l0
        Q = ⟦ stoset→poset isDomStoset ⋆⟧
        _≤Q_ = Poset._≤_ Q
 
        ct = conv {P = ⟦ stoset→poset isDomStoset ⋆⟧} {T = T₀} eq t
        ct' = conv {P = ⟦ stoset→poset isDomStoset ⋆⟧} {T = T₀} eq t'

        ct≈ct' = conv-≈ eq t t' t≈t'

        ct≤ct' : ct ≤Q ct'
        ct≤ct' = (Poset.reflexive Q ct≈ct') 

        ct'≤ct : ct' ≤Q ct
        ct'≤ct = (Poset.reflexive Q $ Poset.Eq.sym Q ct≈ct') 
    --]]]
                
    |i|-injective :
      Injective 
        (preorder→setoid (DeltaPoset.preorder P))
        (preorder→setoid ⟦ ProductPoset (CapsulePoset qAny' (stoset→poset isDomStoset)) (semilat→deltaPoset isCodSemilat) ⋆⟧')
        |i|
    |i|-injective {t , s} {t' , s'} (convt≈convt' , |i|s≈|i|s') = 
      (conv-inj eq t t' convt≈convt' , (proj₂ $ proj₂ $ SemSemilatCore.i ⟦ isCodSemilat Δ⟧) |i|s≈|i|s') 
