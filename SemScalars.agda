module SemScalars where

open import Function using (_$_)
open import Data.Unit hiding (_≤_)
open import Data.List
open import Data.List.All
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import FinPoset
open import Scalars
open import Util
open import UnitPoset
open import Preorders

⟦_q⟧ : q → (Preorder l0 l0 l0 → Preorder l0 l0 l0)
--[[[
⟦_q⟧ qAny P = P'
  where
    |P| : Set
    |P| = Preorder.Carrier P

    ≈-equiv : IsEquivalence (Preorder._≈_ P)
    ≈-equiv = IsPreorder.isEquivalence (Preorder.isPreorder P)

    _∼'_ : |P| → |P| → Set
    p₁ ∼' p₂ = (Preorder._∼_ P p₁ p₂) × (Preorder._∼_ P p₂ p₁)

    trans : ∀ {i j k} → i ∼' j → j ∼' k → i ∼' k
    trans {p₁} {p₂} {p₃} (p₁∼p₂ , p₂∼p₁) (p₂∼p₃ , p₃∼p₂) = (Preorder.trans P p₁∼p₂ p₂∼p₃ , Preorder.trans P p₃∼p₂ p₂∼p₁) 

    P' : Preorder l0 l0 l0
    P' = record
      { Carrier = |P|
      ; _≈_ = Preorder._≈_ P
      ; _∼_ = (λ x y → (Preorder._∼_ P x y) × (Preorder._∼_ P y x)) 
      ; isPreorder = record 
         { isEquivalence = ≈-equiv
          ; reflexive =  λ {i} {j} i≈j → (Preorder.reflexive P i≈j , Preorder.reflexive P (IsEquivalence.sym ≈-equiv i≈j))
          ; trans = trans
         }
      }
⟦_q⟧ qMono P = P  
⟦_q⟧ qAnti P = P' 
  where
    open import Relation.Binary
    open Preorder using (reflexive ; trans)
    
    |P| : Set
    |P| = Preorder.Carrier P

    ≈-equivalence : IsEquivalence (Preorder._≈_ P)
    ≈-equivalence = IsPreorder.isEquivalence (Preorder.isPreorder P) 

    open IsEquivalence ≈-equivalence renaming (sym to ≈-sym)

    _∼_ : |P| → |P| → Set
    _∼_ = Preorder._∼_ P

    _∼'_ : |P| → |P| → Set
    p₁ ∼' p₂ = p₂ ∼ p₁
 
    P' : Preorder l0 l0 l0
    P' = record 
      { Carrier = |P|
      ; _≈_ = Preorder._≈_ P 
      ; _∼_ = _∼'_ 
      ; isPreorder = record 
          { isEquivalence = ≈-equivalence
          ; reflexive =  λ {i} {j} i≈j → Preorder.reflexive P (≈-sym i≈j) 
          ; trans = λ {i} {j} i∼'j j∼'k → Preorder.trans P j∼'k i∼'j 
          }
      }
⟦_q⟧ qConst P = P'
  where
    open import Relation.Binary
    import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as RT

    |P| : Set
    |P| = Preorder.Carrier P

    ≈-equivalence : IsEquivalence (Preorder._≈_ P)
    ≈-equivalence = IsPreorder.isEquivalence (Preorder.isPreorder P)

    _∼_ : |P| → |P| → Set
    _∼_ = Preorder._∼_ P

    _≈_ : |P| → |P| → Set
    _≈_ = Preorder._≈_ P

    closurePreorder : Preorder l0 l0 l0
    closurePreorder = RT.preorder {I = |P|} (λ x y → (x ∼ y) ⊎ (y ∼ x))

    _∼'_ : |P| → |P| → Set
    _∼'_ = Preorder._∼_ closurePreorder 

    reflexive : ∀ {x} {y} → x ≈ y → x ∼' y 
    reflexive {x} {y} x≈y = (inj₁ $ Preorder.reflexive P x≈y) ◅ ε

    P' : Preorder l0 l0 l0
    P' = record
      { Carrier = |P|
      ; _≈_ = _≈_
      ; _∼_ = _∼'_ 
      ; isPreorder = record
        { isEquivalence = ≈-equivalence
        ; reflexive = reflexive
        ; trans = Preorder.trans closurePreorder
        }
      }
--]]]

-- the functor ⟦ q₀ q⟧'s arrow mapping
⟦_q⇒⟧ : (q₀ : q) → (∀ {P Q : Preorder l0 l0 l0} → (P ⇒ Q) → ((⟦ q₀ q⟧ P) ⇒ ⟦ q₀ q⟧ Q))
--[[[
⟦ qMono q⇒⟧ {P} {Q} f = 
  record
  { fun = λ p → |f| p 
  ; monotone = |f|-monotone 
  } 
  where
    |f| = _⇒_.fun f
    |f|-monotone = _⇒_.monotone f
⟦ qAnti q⇒⟧ {P} {Q} f =
  record
  { fun = λ p → |f| p 
  ; monotone = |f|-monotone 
  } 
  where
    |f| = _⇒_.fun f
    |f|-monotone = _⇒_.monotone f
⟦ qConst q⇒⟧ {P} {Q} f =
  record
  { fun = |f|
  ; monotone = gmap' {T = λ x y → x ∼P y ⊎ y ∼P x} {U = λ x y → x ∼Q y ⊎ y ∼Q x} |f| h 
  } 
  where
    open import Data.Unit
    open import Relation.Binary.Construct.Closure.ReflexiveTransitive renaming (map to map' ; gmap to gmap')

    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q

    |f| = _⇒_.fun f
    |f|-monotone = _⇒_.monotone f
    
    _∼P_ : |P| → |P| → Set
    _∼P_ = Preorder._∼_ P

    _∼Q_ : |Q| → |Q| → Set
    _∼Q_ = Preorder._∼_ Q

    h : ∀ {x y} → (x ∼P y ⊎ y ∼P x) → (|f| x ∼Q |f| y ⊎ |f| y ∼Q |f| x)
    h {x} {y} (inj₁ x∼y) = inj₁ $ |f|-monotone x∼y
    h {x} {y} (inj₂ y∼x) = inj₂ $ |f|-monotone y∼x
 
⟦ qAny q⇒⟧ {P} {Q} f =
  record
  { fun = |f|
  ; monotone = monotone 
  } 
  where
    open import Function using (_$_)

    |f| = _⇒_.fun f
    |f|-monotone = _⇒_.monotone f

    monotone : (Preorder._∼_ $ ⟦ qAny q⟧ P) =[ |f| ]⇒ (Preorder._∼_ $ ⟦ qAny q⟧ Q)
    monotone {p₁} {p₂} (p₁∼p₂ , p₂∼p₁) = (|f|-monotone p₁∼p₂ , |f|-monotone p₂∼p₁)
--]]]

⟦_q≤_⟧ : (q₁ q₂ : q) → Set₁
⟦ q₁ q≤ q₂ ⟧  = ∀ (P : Preorder l0 l0 l0) → (⟦ q₂ q⟧ P) ⇒ (⟦ q₁ q⟧ P)

q≤⟦_⟧ : ∀ {q₁} {q₂} → q₁ q≤ q₂ → ⟦ q₁ q≤ q₂ ⟧
--[[[
q≤⟦_⟧ {q₁} {q₂} q₁≤q₂ = QP.makeInterpretation ⟦_q≤_⟧ (λ {q₁} {q₂} {q₃} → comp {q₁} {q₂} {q₃}) (λ {q} → qRefl {q}) ⟦covers⟧ q₁≤q₂ 
  where
    comp : {q₁ q₂ q₃ : q} → ⟦ q₁ q≤ q₂ ⟧ → ⟦ q₂ q≤ q₃ ⟧ → ⟦ q₁ q≤ q₃ ⟧ 
    comp {q₁} {q₂} {q₃} ⟦q₁≤q₂⟧ ⟦q₂≤q₃⟧ P = (⟦q₁≤q₂⟧ P) ∘ (⟦q₂≤q₃⟧ P)

    qRefl : {q₀ : q} → ⟦ q₀ q≤ q₀ ⟧
    qRefl P = id

    ⟦covers⟧ : All (λ cov → ⟦ (Cover.lo cov) q≤ (Cover.hi cov) ⟧) covers
    ⟦covers⟧ = x1 ∷ x2 ∷ x3 ∷ (λ P → x4 P) ∷ []
      where
        x1 : ⟦ qMono q≤ qAny ⟧
        x1 P = record 
          { fun = λ p → p
          ; monotone = λ {p} {q} p≤q×q≤p → proj₁ p≤q×q≤p 
          }

        x2 : ⟦ qAnti q≤ qAny ⟧
        x2 P = record
          { fun = λ p → p
          ; monotone = λ {p} {q} p≤q×q≤p → proj₂ p≤q×q≤p
          }

        x3 : ⟦ qConst q≤ qMono ⟧
        x3 P = record
          { fun = λ p → p
          ; monotone = λ {p} {q} p≤q → inj₁ p≤q ◅ ε
          }
          where
            open import Data.Unit
            open import Relation.Binary.Construct.Closure.ReflexiveTransitive

        x4 : ⟦ qConst q≤ qAnti ⟧
        x4 P = record
          { fun = λ p → p
          ; monotone = λ {p} {q} q≤p → inj₂ q≤p ◅ ε
          }
          where
            open import Data.Unit
            open import Relation.Binary.Construct.Closure.ReflexiveTransitive
--]]]

-- note: technically, to be cartesian the functor also must preserve unit
q-cartesian⃗ : (P Q : Preorder l0 l0 l0) → (t₀ : q) → (⟦ t₀ q⟧ $ ×-preorder P Q) ⇒ (×-preorder (⟦ t₀ q⟧ P) (⟦ t₀ q⟧ Q))
--[[[
q-cartesian⃗ P Q qAny = 
  record
  { fun = λ x → x
  ; monotone = λ x≤y×y≤x → (proj₁ (proj₁ x≤y×y≤x) , proj₁ (proj₂ x≤y×y≤x)) , (proj₂ (proj₁ x≤y×y≤x) , proj₂ (proj₂ x≤y×y≤x))
  }
q-cartesian⃗ P Q qMono = 
  record
  { fun = λ x → x
  ; monotone = λ x≤y → x≤y
  }
q-cartesian⃗ P Q qAnti = 
  record
  { fun = λ x → x
  ; monotone = λ x≤y → x≤y
  }
q-cartesian⃗ P Q qConst =
  record
  { fun = λ x → x
  ; monotone = λ x∼y → (gmap proj₁ h1 x∼y , gmap proj₂ h2 x∼y) 
  }
  where
    open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (gmap)

    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q

    open Preorder (×-preorder P Q) renaming (_∼_ to _∼PQ_)
    open Preorder P renaming (_∼_ to _∼P_)
    open Preorder Q renaming (_∼_ to _∼Q_)

    h1 : (λ x y → x ∼PQ y ⊎ y ∼PQ x) =[ proj₁ ]⇒ (λ x y → x ∼P y ⊎ y ∼P x)
    h1 (inj₁ (p₁∼p₂ , q₁∼q₂)) = inj₁ p₁∼p₂
    h1 (inj₂ (p₂∼p₁ , q₂∼q₁)) = inj₂ p₂∼p₁

    h2 : (λ x y → x ∼PQ y ⊎ y ∼PQ x) =[ proj₂ ]⇒ (λ x y → x ∼Q y ⊎ y ∼Q x)
    h2 (inj₁ (p₁∼p₂ , q₁∼q₂)) = inj₁ q₁∼q₂
    h2 (inj₂ (p₂∼p₁ , q₂∼q₁)) = inj₂ q₂∼q₁
--]]]

q-cartesian⃖ : (P Q : Preorder l0 l0 l0) → (t₀ : q) → (×-preorder (⟦ t₀ q⟧ P) (⟦ t₀ q⟧ Q)) ⇒ (⟦ t₀ q⟧ $ ×-preorder P Q)
--[[[
q-cartesian⃖ P Q qAny =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun = λ x → x

    monotone : (Preorder._∼_ (×-preorder (⟦ qAny q⟧ P) (⟦ qAny q⟧ Q))) =[ fun ]⇒ (Preorder._∼_ $ ⟦ qAny q⟧ $ ×-preorder P Q)
    monotone ((p₁∼p₂ , p₂∼p₁) , (q₁∼q₂ , q₂∼q₁)) = ((p₁∼p₂ , q₁∼q₂) , (p₂∼p₁ , q₂∼q₁))
q-cartesian⃖ P Q qMono =
  record
  { fun = λ x → x
  ; monotone = λ x≤y → x≤y
  }
q-cartesian⃖ P Q qAnti =
  record
  { fun = λ x → x
  ; monotone = λ x≤y → x≤y
  }
q-cartesian⃖ P Q qConst =
  record
  { fun = fun
  ; monotone = monotone 
  }
  where
    fun = λ x → x

    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q

    monotone' : ∀ {p₁ p₂ q₁ q₂} → 
                (Preorder._∼_ (⟦ qConst q⟧ P) p₁ p₂) → (Preorder._∼_ (⟦ qConst q⟧ Q) q₁ q₂) → 
                (Preorder._∼_ (⟦ qConst q⟧ $ ×-preorder P Q) (p₁ , q₁) (p₂ , q₂))
    monotone' {p₁} {.p₁} {q₁} {.q₁} ε ε = ε
    monotone' {p₁} {.p₁} {q₁} {q₂} ε (inj₁ q₁∼ ◅ q₁∼q₂') = inj₁ (Preorder.refl P , q₁∼) ◅ monotone' ε q₁∼q₂'
    monotone' {p₁} {.p₁} {q₁} {q₂} ε (inj₂ ∼q₁ ◅ q₁∼q₂') = inj₂ (Preorder.refl P , ∼q₁) ◅ monotone' ε q₁∼q₂'
    monotone' {p₁} {p₂} {q₁} {.q₁} (inj₁ p₁∼ ◅ p₁∼p₂') ε = inj₁ (p₁∼ , Preorder.refl Q) ◅ monotone' p₁∼p₂' ε
    monotone' {p₁} {p₂} {q₁} {.q₁} (inj₂ ∼p₁ ◅ p₁∼p₂') ε = inj₂ (∼p₁ , Preorder.refl Q) ◅ monotone' p₁∼p₂' ε
    monotone' {p₁} {p₂} {q₁} {q₂} (inj₁ p₁∼ ◅ p₁∼p₂') (inj₁ q₁∼ ◅ q₁∼q₂') = 
      inj₁ (p₁∼ , Preorder.refl Q) ◅ inj₁ (Preorder.refl P , q₁∼) ◅ monotone' p₁∼p₂' q₁∼q₂' 
    monotone' {p₁} {p₂} {q₁} {q₂} (inj₁ p₁∼ ◅ p₁∼p₂') (inj₂ ∼q₁ ◅ q₁∼q₂') = 
      inj₁ (p₁∼ , Preorder.refl Q) ◅ inj₂ (Preorder.refl P , ∼q₁) ◅ monotone' p₁∼p₂' q₁∼q₂'
    monotone' {p₁} {p₂} {q₁} {q₂} (inj₂ ∼p₁ ◅ p₁∼p₂') (inj₁ q₁∼ ◅ q₁∼q₂') = 
      inj₂ (∼p₁ , Preorder.refl Q) ◅ inj₁ (Preorder.refl P , q₁∼) ◅ monotone' p₁∼p₂' q₁∼q₂'
    monotone' {p₁} {p₂} {q₁} {q₂} (inj₂ ∼p₁ ◅ p₁∼p₂') (inj₂ ∼q₁ ◅ q₁∼q₂') = 
      inj₂ (∼p₁ , Preorder.refl Q) ◅ inj₂ (Preorder.refl P , ∼q₁) ◅ monotone' p₁∼p₂' q₁∼q₂'  

    monotone : (Preorder._∼_ (×-preorder (⟦ qConst q⟧ P) (⟦ qConst q⟧ Q))) =[ fun ]⇒ (Preorder._∼_ $ ⟦ qConst q⟧ $ ×-preorder P Q)
    monotone (p₁∼p₂ , q₁∼q₂) = monotone' p₁∼p₂ q₁∼q₂
--]]]

-- comultiplication
δ : (t₁ t₂ : q) → (P : Preorder l0 l0 l0) → (⟦ t₁ q∘ t₂ q⟧ P) ⇒ (⟦ t₁ q⟧ $ ⟦ t₂ q⟧ P)
--[[[
δ qMono qMono P = id
δ qMono qAnti P = id
δ qMono qConst P = id
δ qMono qAny P = id
δ qAnti qMono P = id
δ qAnti qAnti P =
  record
  { fun = λ x → x
  ; monotone = λ {x} {y} x≤y → x≤y
  }
δ qAnti qConst P =
  record
  { fun = λ x → x
  ; monotone = λ {x} {y} x∼y → RT.reverse rev x∼y 
  }
  where
    open Preorder P
    import Relation.Binary.Construct.Closure.ReflexiveTransitive as RT

    rev : ∀ {p₁ p₂} → (p₁ ∼ p₂ ⊎ p₂ ∼ p₁) → (p₂ ∼ p₁ ⊎ p₁ ∼ p₂)
    rev (inj₁ p₁∼p₂) = inj₂ p₁∼p₂
    rev (inj₂ p₂∼p₁) = inj₁ p₂∼p₁
δ qAnti qAny P =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Preorder.Carrier $ ⟦ qAny q⟧ P) → (Preorder.Carrier $ ⟦ qAnti q⟧ $ ⟦ qAny q⟧ P) 
    fun x = x

    monotone : (Preorder._∼_ $ ⟦ qAny q⟧ P) =[ fun ]⇒ (Preorder._∼_ $ ⟦ qAnti q⟧ $ ⟦ qAny q⟧ P) 
    monotone {x} {y} (x∼y , y∼x) = y∼x , x∼y
δ qConst qMono P =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Preorder.Carrier $ ⟦ qMono q⟧ P) → (Preorder.Carrier $ ⟦ qConst q⟧ $ ⟦ qMono q⟧ P) 
    fun x = x

    monotone : (Preorder._∼_ $ ⟦ qMono q⟧ P) =[ fun ]⇒ (Preorder._∼_ $ ⟦ qConst q⟧ $ ⟦ qMono q⟧ P) 
    monotone {x} {y} x∼y = (inj₁ x∼y) ◅ ε
δ qConst qAnti P =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Preorder.Carrier $ ⟦ qAnti q⟧ P) → (Preorder.Carrier $ ⟦ qConst q⟧ $ ⟦ qAnti q⟧ P) 
    fun x = x

    monotone : (Preorder._∼_ $ ⟦ qAnti q⟧ P) =[ fun ]⇒ (Preorder._∼_ $ ⟦ qConst q⟧ $ ⟦ qAnti q⟧ P) 
    monotone {x} {y} x∼y = (inj₁ x∼y) ◅ ε
δ qConst qConst P =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Preorder.Carrier $ ⟦ qConst q⟧ P) → (Preorder.Carrier $ ⟦ qConst q⟧ $ ⟦ qConst q⟧ P)
    fun x = x

    monotone : (Preorder._∼_ $ ⟦ qConst q⟧ P) =[ fun ]⇒ (Preorder._∼_ $ ⟦ qConst q⟧ $ ⟦ qConst q⟧ P)
    monotone {x} {y} x∼y = (inj₁ x∼y) ◅ ε
δ qConst qAny P =
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Preorder.Carrier $ ⟦ qAny q⟧ P) → (Preorder.Carrier $ ⟦ qConst q⟧ $ ⟦ qAny q⟧ P)
    fun x = x

    monotone : (Preorder._∼_ $ ⟦ qAny q⟧ P) =[ fun ]⇒ (Preorder._∼_ $ ⟦ qConst q⟧ $ ⟦ qAny q⟧ P)
    monotone {x} {y} (x∼y , y∼x) = (inj₁ $ x∼y , y∼x) ◅ ε
δ qAny qMono P = id
δ qAny qAnti P = 
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Preorder.Carrier $ ⟦ qAny q⟧ P) → (Preorder.Carrier $ ⟦ qAny q⟧ $ ⟦ qAnti q⟧ P)
    fun x = x

    monotone : (Preorder._∼_ $ ⟦ qAny q⟧ P) =[ fun ]⇒ (Preorder._∼_ $ ⟦ qAny q⟧ $ ⟦ qAnti q⟧ P)
    monotone {x} {y} (x∼y , y∼x) = (y∼x , x∼y)
δ qAny qConst P = 
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    import Relation.Binary.Construct.Closure.ReflexiveTransitive as RT
    open Preorder P

    rev : ∀ {p₁ p₂} → (p₁ ∼ p₂ ⊎ p₂ ∼ p₁) → (p₂ ∼ p₁ ⊎ p₁ ∼ p₂)
    rev (inj₁ p₁∼p₂) = inj₂ p₁∼p₂
    rev (inj₂ p₂∼p₁) = inj₁ p₂∼p₁

    fun : (Preorder.Carrier $ ⟦ qConst q⟧ P) → (Preorder.Carrier $ ⟦ qAny q⟧ $ ⟦ qConst q⟧ P) 
    fun x = x

    monotone : (Preorder._∼_ $ ⟦ qConst q⟧ P) =[ fun ]⇒ (Preorder._∼_ $ ⟦ qAny q⟧ $ ⟦ qConst q⟧ P) 
    monotone {x} {y} x∼y = (x∼y , RT.reverse rev x∼y)
δ qAny qAny P = 
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    fun : (Preorder.Carrier $ ⟦ qAny q⟧ P) → (Preorder.Carrier $ ⟦ qAny q⟧ $ ⟦ qAny q⟧ P) 
    fun x = x

    monotone : (Preorder._∼_ $ ⟦ qAny q⟧ P) =[ fun ]⇒ (Preorder._∼_ $ ⟦ qAny q⟧ $ ⟦ qAny q⟧ P) 
    monotone {x} {y} (x∼y , y∼x) = ((x∼y , y∼x) , (y∼x , x∼y))
--]]]

q-preserves-+⃗ : (P Q : Preorder l0 l0 l0) → (t₀ : q) → (⟦ t₀ q⟧ $ ⊎-preorder0 P Q) ⇒ (⊎-preorder0 (⟦ t₀ q⟧ P) (⟦ t₀ q⟧ Q))
q-preserves-+⃗ P Q qMono = id
q-preserves-+⃗ P Q qAnti = 
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    open import Relation.Binary
    open import Data.Sum
    open import Data.Sum.Relation.Pointwise

    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q

    isPartialOrder-P : IsPreorder (Preorder._≈_ P) (Preorder._∼_ P)
    isPartialOrder-P = Preorder.isPreorder P

    fun : (|P| ⊎ |Q|) → (|P| ⊎ |Q|)
    fun x = x

    monotone : (Preorder._∼_ $ ⟦ qAnti q⟧ $ ⊎-preorder0 P Q) =[ fun ]⇒ (Preorder._∼_ $ ⊎-preorder0 (⟦ qAnti q⟧ P) (⟦ qAnti q⟧ Q))
    monotone {inj₁ x} {inj₂ y} ()
    monotone {inj₁ x} {inj₁ y} (inj₁ y≤x) = inj₁ y≤x
    monotone {inj₂ x} {inj₂ y} (inj₂ y≤x) = inj₂ y≤x
q-preserves-+⃗ P Q qConst = 
  record
  { fun = fun
  ; monotone = monotone 
  }
  where
    open import Data.Sum.Relation.Pointwise

    ∗ = ⟦ qConst q⟧
    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q

    fun : (|P| ⊎ |Q|) → (|P| ⊎ |Q|)
    fun x = x

    monotone : (Preorder._∼_ $ ∗ $ ⊎-preorder0 P Q) =[ fun ]⇒ (Preorder._∼_ $ ⊎-preorder0 (∗ P) (∗ Q))
    monotone {inj₁ p₁} {inj₁ p₂} ε = inj₁ ε
    monotone {inj₁ p₁} {inj₁ p₂} (inj₁ (inj₁ p₁∼) ◅ p₁∼p₂') with monotone p₁∼p₂'
    monotone {inj₁ p₁} {inj₁ p₂} (inj₁ (inj₁ p₁∼) ◅ _) | inj₁ p₁∼p₂' = inj₁ (inj₁ p₁∼ ◅ p₁∼p₂')
    monotone {inj₁ p₁} {inj₁ p₂} (inj₂ (inj₁ ∼p₁) ◅ p₁∼p₂') with monotone p₁∼p₂'
    monotone {inj₁ p₁} {inj₁ p₂} (inj₂ (inj₁ ∼p₁) ◅ _) | inj₁ p₁∼p₂' = inj₁ (inj₂ ∼p₁ ◅ p₁∼p₂')
    monotone {inj₁ p} {inj₂ q} (_ ◅ p∼q') with monotone p∼q'
    monotone {inj₁ p} {inj₂ q} (inj₁ () ◅ _) | inj₂ _ --= {!!}
    monotone {inj₁ p} {inj₂ q} (inj₂ () ◅ _) | inj₂ _
    monotone {inj₂ q₁} {inj₁ p₂} (inj₁ (inj₂ q₁∼) ◅ q₁∼p₂') with monotone q₁∼p₂'
    monotone {inj₂ q₁} {inj₁ p₂} (inj₁ (inj₂ q₁∼) ◅ _) | () 
    monotone {inj₂ q₁} {inj₁ p₂} (inj₂ (inj₂ ∼q₁) ◅ q₁∼p₂') with monotone q₁∼p₂'
    monotone {inj₂ q₁} {inj₁ p₂} (inj₂ (inj₂ ∼q₁) ◅ _) | ()
    monotone {inj₂ q₁} {inj₂ q₂} ε = inj₂ ε
    monotone {inj₂ q₁} {inj₂ q₂} (inj₁ (inj₂ q₁∼) ◅ q₁∼q₂') with monotone q₁∼q₂'
    monotone {inj₂ q₁} {inj₂ q₂} (inj₁ (inj₂ q₁∼) ◅ _) | inj₂ q₁∼q₂' = inj₂ (inj₁ q₁∼ ◅ q₁∼q₂')
    monotone {inj₂ q₁} {inj₂ q₂} (inj₂ (inj₂ ∼q₁) ◅ q₁∼q₂') with monotone q₁∼q₂'
    monotone {inj₂ q₁} {inj₂ q₂} (inj₂ (inj₂ ∼q₁) ◅ _) | inj₂ q₁∼q₂' = inj₂ (inj₂ ∼q₁ ◅ q₁∼q₂')
q-preserves-+⃗ P Q qAny = 
  record
  { fun = fun
  ; monotone = monotone
  }
  where
    open import Data.Sum.Relation.Pointwise
    ⁇ = ⟦ qAny q⟧
    |P| = Preorder.Carrier P
    |Q| = Preorder.Carrier Q

    fun : (|P| ⊎ |Q|) → (|P| ⊎ |Q|)
    fun x = x

    monotone : (Preorder._∼_ $ ⁇ $ ⊎-preorder0 P Q) =[ fun ]⇒ (Preorder._∼_ $ ⊎-preorder0 (⁇ P) (⁇ Q))
    monotone {inj₁ p₁} {inj₁ p₂} (inj₁ p₁∼p₂ , inj₁ p₂∼p₁) = inj₁ (p₁∼p₂ , p₂∼p₁)
    monotone {inj₂ q₁} {inj₁ p₂} ()
    monotone {inj₂ q₁} {inj₂ q₂} (inj₂ q₁∼q₂ , inj₂ q₂∼q₁) = inj₂ (q₁∼q₂ , q₂∼q₁) 

