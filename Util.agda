module Util where

open import Function using (_∘_ ; _$_)
open import Function.Equality using (_⟨$⟩_)

open import Data.Maybe hiding (Eq)
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Agda.Builtin.Equality
open import Data.Fin as F
open import Data.Nat as N
open import Data.Nat.Properties as NP
open import Relation.Binary
open import Relation.Nullary
open import Relation.Unary hiding (_⇒_ ; Decidable ; _∈_ )
open import Data.Vec as V hiding ([_] ; _++_ ; reverse ; _∷ʳ_ ; _∈_)
open import Data.List as L
open import Data.List.Properties as LP
open import Data.List.Any as LA
open import Data.List.Any.Properties as LAP
open import Data.List.Membership.Propositional using (_∈_)
open import Level renaming (zero to ℓ₀; suc to lsuc)
open import Relation.Binary.PropositionalEquality as PE hiding ( [_] )  
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Binary.PropositionalEquality.Core as PEC

open import Data.List.All as LL
open import Data.Vec.All as VL

-- this is called the inspect idiom in the Agda stdlib
keep : ∀{ℓ}{A : Set ℓ} → (x : A) → Σ A (λ y → x ≡ y)
keep {ℓ} {A} x = ( x , refl )

l0 l1 l2 l3 : Level
l0 = ℓ₀
l1 = lsuc ℓ₀
l2 = lsuc (lsuc ℓ₀)
l3 = lsuc (lsuc (lsuc ℓ₀))

pred! : {l : ℕ} → (m : F.Fin (suc l)) → {n : Fin′ m} → Fin l   
pred! zero {()}
pred! (suc m) = m

decEquiv : ∀ {ℓ} {A B : Set} {R Q : REL A B ℓ} → (imp1 : R ⇒ Q) → (imp2 : Q ⇒ R) → (d : Decidable R) → Decidable Q
decEquiv {ℓ} {A} {B} {R} {Q} imp1 imp2 d = decidableQ
  where
    decidableQ : Decidable Q
    decidableQ a b with (d a b)
    decidableQ a b | yes aRb = yes (imp1 aRb)
    decidableQ a b | no ¬aRb = no (¬aRb ∘ imp2)

_≤′?_ : Decidable _≤′_
_≤′?_ = decEquiv ≤⇒≤′ ≤′⇒≤ N._≤?_

AnyEliminator : ∀ (A B : Set) → (P : Pred A ℓ₀) → (l : List A) → Set₁
AnyEliminator A B P l = 
  (a : A) → 
  (f : (Q : Pred A ℓ₀) → Q a → LA.Any Q l) → 
  (p : P a) →
  (a∈l : a ∈ l) →
  B


shift : ∀ {ℓ} {A : Set ℓ} {l : List A} → (prev rest' : List A) → (a : A) → (p : l ≡ (reverse prev) ++ (a ∷ rest'))
            → (l ≡ (reverse $ a ∷ prev) ++ rest')
shift {A = A} {l} prev rest' a p = ret
  where
    open import Algebra
    open Monoid (LP.++-monoid A)
    rev : (reverse $ a ∷ prev) ≡ (reverse prev) ∷ʳ a
    rev = LP.unfold-reverse a prev
    ret : l ≡ reverse (a ∷ prev) ++ rest'
    ret rewrite rev | (assoc (reverse prev) [ a ] rest')  = p

anyEliminate : ∀ {A B : Set} {P : Pred A ℓ₀}  → 
                  (l : List A) → 
                  AnyEliminator A B P l →
                  LA.Any P l →
                  B

anyEliminate {A} {B} {P} l eliminator any-P-l = elimAux l any-P-l [] PE.refl
  where
    open import Algebra
    open Monoid (LP.++-monoid A)

    elimAux : (as : List A) → (any-P-as : LA.Any P as) → (prev-as : List A) → (p : l ≡ (reverse prev-as) ++ as) → B 
    elimAux .(a ∷ as') (here {x = a} {xs = as'} pa) prev-as p =
      eliminator a f pa a∈l
      where
        open import Function.Inverse
        f : (Q : Pred A ℓ₀) → Q a → LA.Any Q l
        f Q qa rewrite p = (Inverse.to equiv) ⟨$⟩ (inj₂ $ here qa) 
          where
            equiv : (LA.Any Q (reverse prev-as) ⊎ LA.Any Q (a ∷ as')) ↔ LA.Any Q ((reverse prev-as) ++ (a ∷ as'))
            equiv = LAP.++↔
        a∈l : a ∈ l
        a∈l rewrite p = ++⁺ʳ (reverse prev-as) (LA.here PE.refl) 
    elimAux .(a ∷ as') (there {x = a} {xs = as'} any-P-as') prev-as p =
      elimAux as' any-P-as' (a ∷ prev-as) (shift prev-as as' a p)

length-∷ʳ : ∀ {a} {A : Set a} → (l : List A) → (a : A) → (L.length (l ∷ʳ a) ≡ N.suc (L.length l))
length-∷ʳ l a = begin
    L.length (l ∷ʳ a) ≡⟨ PE.refl ⟩
    L.length (l ++ L.[ a ]) ≡⟨ length-++ l ⟩ 
    (L.length l) N.+ (L.length L.[ a ]) ≡⟨ PE.refl  ⟩
    (L.length l) N.+ 1 ≡⟨ NP.+-comm (L.length l) 1 ⟩
    1 N.+ (L.length l) ≡⟨ PE.refl ⟩
    suc (L.length l)
   ∎
  where
    open ≡-Reasoning
    open import Algebra
    open CommutativeSemiring (NP.commutativeSemiring) hiding (_+_)

lengthReverse : ∀ {a} {A : Set a} → (l : List A) → (L.length l ≡ L.length (L.reverse l))
lengthReverse (a ∷ as) = begin 
    L.length (a ∷ as) ≡⟨ PE.refl ⟩
    N.suc (L.length as) ≡⟨ PE.cong N.suc (lengthReverse as) ⟩
    (N.suc (L.length (L.reverse as))) ≡⟨ PE.sym $ length-∷ʳ (L.reverse as) a ⟩
    L.length ((L.reverse as) ∷ʳ a) ≡⟨ cong L.length (PE.sym $ LP.unfold-reverse a as) ⟩
    (L.length $ L.reverse (a ∷ as))
   ∎
  where
    open ≡-Reasoning
    open import Algebra
    open CommutativeSemiring (NP.commutativeSemiring) hiding (_+_)
lengthReverse [] = refl

allReverse : ∀ {a p} {A : Set a} → (l : List A) → (P : A → Set p) → (lAll : LL.All P l) → LL.All P (reverse l)
allReverse {A = A} l P lAll = allReverseAux [] l (proj₁ identity $ l) [] lAll 
  where
    open import Algebra
    open Monoid (LP.++-monoid A)
    open ≡-Reasoning
    allReverseAux : (prev : List A) → (rest : List A) → (p : l ≡ (reverse prev) ++ rest) → (allPrev : LL.All P prev) →
      (allRest : LL.All P rest) → LL.All P $ reverse l
    allReverseAux prev (a ∷ rest) p allPrev (P-a ∷ P-rest) = 
      allReverseAux (a ∷ prev) rest (shift prev rest a p) (P-a ∷ allPrev) P-rest
    allReverseAux prev [] p allPrev [] = subst (LL.All P) (PE.sym p3) allPrev 
      where
        p1 : l ≡ (reverse prev)
        p1 rewrite (proj₂ identity $ reverse prev) = p 

        p2 : reverse l ≡ reverse (reverse prev)
        p2 = cong reverse p1

        p3 : reverse l ≡ prev
        p3 = begin
          reverse l ≡⟨ p2 ⟩
          reverse (reverse prev) ≡⟨ LP.reverse-involutive prev ⟩
          prev
         ∎

allListToVec : ∀ {a p} {A : Set a} → (l : List A) → (P : A → Set p) → (lAll : LL.All P l) → VL.All P (V.fromList l)
allListToVec (a ∷ rest) P (P-a ∷ P-rest) =  P-a ∷ (allListToVec rest P P-rest)
allListToVec [] P [] = []

list-tofrom-adj : ∀ {ℓ} {A : Set ℓ} → (l₀ : List A) → (v : Vec A $ L.length l₀) → 
                      (p : V.toList v ≡ l₀) → (v ≡ V.fromList l₀)

list-tofrom-adj (la₀ ∷ l₀') (va ∷ v') p with r
  where
    q : va ∷ V.toList v' ≡ la₀ ∷ l₀'
    q = p

    r : va ≡ la₀
    r = proj₁ (∷-injective q)

list-tofrom-adj (la₀ ∷ l₀') (.la₀ ∷ v') p | PE.refl = cong (la₀ ∷_) rec    
  where
    q : la₀ ∷ V.toList v' ≡ la₀ ∷ l₀'
    q = p

    p' : V.toList v' ≡ l₀'
    p' = proj₂ (∷-injective q)  

    rec : v' ≡ (V.fromList l₀')
    rec = list-tofrom-adj l₀' v' p'       

list-tofrom-adj [] [] p = refl


list-tofrom-adj2 : ∀ {ℓ} {A : Set ℓ} → (l₀ l₁ : List A) → (v : Vec A $ (L.length l₀) N.+ (L.length l₁)) → 
                      (p : V.toList v ≡ l₀ L.++ l₁) → (v ≡ (V.fromList l₀) V.++ (V.fromList l₁))

list-tofrom-adj2 (la₀ ∷ l₀') l₁ (va ∷ v') p with r 
  where
    q : va ∷ V.toList v' ≡ la₀ ∷ (l₀' ++ l₁)
    q = p

    r : va ≡ la₀
    r = proj₁ (∷-injective q)

list-tofrom-adj2 (la₀ ∷ l₀') l₁ (.la₀ ∷ v') p | PE.refl = cong (la₀ ∷_) rec    
  where
    q : la₀ ∷ V.toList v' ≡ la₀ ∷ (l₀' ++ l₁)
    q = p

    p' : V.toList v' ≡ l₀' L.++ l₁
    p' = proj₂ (∷-injective q)  

    rec : v' ≡ (V.fromList l₀') V.++ (V.fromList l₁)
    rec = list-tofrom-adj2 l₀' l₁ v' p'       

list-tofrom-adj2 [] l₁ v p = list-tofrom-adj l₁ v p

toList-length : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → (v : Vec A n) → (L.length (V.toList v) ≡ n)
toList-length (a ∷ v') = cong suc (toList-length v')
toList-length [] = refl

imagePreorder : ∀ {ℓ₀ ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₀} {B : Set ℓ₁} → (_B≤_ : Rel B ℓ₂) → (_B≈_ : Rel B ℓ₃) → 
                  (pB : IsPreorder _B≈_ _B≤_) → (f : A → B) →
                  (Σ (Rel A ℓ₂) (λ Q → IsPreorder _≡_ Q))

imagePreorder {ℓ₀} {ℓ₁} {ℓ₂} {ℓ₃} {A} {B} _B≤_ _B≈_ preorderB f = ( _A≤_ , preorderA )
  where
    _A≤_ : Rel A _
    a₀ A≤ a₁ = (f a₀) B≤ (f a₁)

    A≤-refl : _≡_ ⇒ _A≤_ -- ∀ {i j} → i ≡ j → i A≤ j
    A≤-refl {i} .{i} refl = (IsPreorder.reflexive preorderB) fi-B≈-fi
      where
        B≈-refl : Reflexive _B≈_
        B≈-refl = IsEquivalence.refl (IsPreorder.isEquivalence preorderB)

        fi-B≈-fi : (f i) B≈ (f i)
        fi-B≈-fi = B≈-refl

    A≤-trans : Transitive _A≤_ -- ∀ {i j k} → i A≤ j → j A≤ k → i A≤ k 
    A≤-trans {i} {j} {k} i≤j j≤k = (IsPreorder.trans preorderB) i≤j j≤k  

    preorderA : IsPreorder _≡_ _A≤_
    preorderA = record {
       isEquivalence = PEC.isEquivalence ;
       reflexive = A≤-refl ;
       trans = A≤-trans
     }

------------------- Strict total order for unit

module UnitStrictTotal where
  open import Data.Unit
  
  -- no pair of units is in the strict less-than relation
  -- hence no constructors
  data _lt_ (x y : ⊤) : Set where

  lt-isTransitive : Transitive _lt_
  lt-isTransitive () () 
  
  lt-trichotomous : Trichotomous _≡_ _lt_
  lt-trichotomous x y = tri≈ (λ ()) refl (λ ())
 
  ≡-isEquivalence : IsEquivalence {A = ⊤} _≡_
  ≡-isEquivalence = PE.isEquivalence
  
  ⊤-IsStrictTotalOrder : IsStrictTotalOrder _≡_ _lt_
  ⊤-IsStrictTotalOrder = 
    record{ 
      isEquivalence = ≡-isEquivalence;
      trans = lt-isTransitive;
      compare = lt-trichotomous
     }

  ⊤-strictTotalOrder : StrictTotalOrder l0 l0 l0
  ⊤-strictTotalOrder =
    record{
      Carrier = ⊤;
      _≈_ = _≡_;
      _<_ = _lt_;
      isStrictTotalOrder = ⊤-IsStrictTotalOrder
     }
