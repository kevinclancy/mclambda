module Util where

open import Function using (_∘_ ; _$_)
open import Function.Equality using (_⟨$⟩_)

open import Data.Maybe
open import Data.Bool hiding (_∨_)
open import Data.Product
open import Data.Sum
open import Agda.Builtin.Equality
open import Data.Fin as F
open import Data.Nat as N hiding (_⊔_)
open import Data.Nat.Properties as NP
open import Relation.Binary
open import Relation.Nullary
open import Relation.Unary hiding (_⇒_ ; Decidable ; _∈_ )
open import Data.Vec as V hiding ([_] ; _++_ ; reverse ; _∷ʳ_)
open import Data.List as L
open import Data.List.Properties as LP
open import Data.List.Any as LA
open import Data.List.Any.Properties as LAP
open import Data.List.Membership.Propositional using (_∈_)
open import Level renaming (zero to ℓ₀; suc to lsuc)
open import Relation.Binary.PropositionalEquality as PE hiding ( [_] )  
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Binary.PropositionalEquality.Core as PEC

open import Data.List.Relation.Pointwise as LPW hiding (refl ; rec ; Rel)
open import Data.List.All as LL
open import Data.Vec.All as VL
open import Data.Empty

open import Relation.Binary.Lattice

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

--_≤′?_ : Decidable _≤′_
--_≤′?_ = decEquiv ≤⇒≤′ ≤′⇒≤ N._≤?_

AnyEliminator : ∀ {ℓQ ℓP ℓA ℓB} → (A : Set ℓA) → (B : Set ℓB) → (P : Pred A ℓP) → (l : List A) → Set _
AnyEliminator {ℓQ} A B P l = 
  (a : A) → 
  (f : (Q : Pred A ℓQ) → Q a → LA.Any Q l) → 
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

anyEliminate : ∀ {ℓQ ℓP ℓA ℓB} → {A : Set ℓA} → {B : Set ℓB} → {P : Pred A ℓP}  → 
                  (l : List A) → 
                  AnyEliminator {ℓQ} {ℓP} {ℓA} {ℓB} A B P l →
                  LA.Any P l →
                  B

anyEliminate {ℓQ} {ℓP} {ℓA} {ℓB} {A} {B} {P} l eliminator any-P-l = elimAux l any-P-l [] PE.refl
  where
    open import Algebra
    open Monoid (LP.++-monoid A)

    elimAux : (as : List A) → (any-P-as : LA.Any P as) → (prev-as : List A) → (p : l ≡ (reverse prev-as) ++ as) → B 
    elimAux .(a ∷ as') (here {x = a} {xs = as'} pa) prev-as p =
      eliminator a f pa a∈l
      where
        open import Function.Inverse
        f : (Q : Pred A ℓQ) → Q a → LA.Any Q l
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
    open CommutativeSemiring (NP.*-+-commutativeSemiring) hiding (_+_)

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
    open CommutativeSemiring (NP.*-+-commutativeSemiring) hiding (_+_)
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
  data _⊤<_ (x y : ⊤) : Set where

  ⊤<-isTransitive : Transitive _⊤<_
  ⊤<-isTransitive () () 
  
  ⊤<-trichotomous : Trichotomous _≡_ _⊤<_
  ⊤<-trichotomous x y = tri≈ (λ ()) refl (λ ())
 
  ≡-isEquivalence : IsEquivalence {A = ⊤} _≡_
  ≡-isEquivalence = PE.isEquivalence
  
  ⊤-IsStrictTotalOrder : IsStrictTotalOrder _≡_ _⊤<_
  ⊤-IsStrictTotalOrder = 
    record{ 
      isEquivalence = ≡-isEquivalence;
      trans = ⊤<-isTransitive;
      compare = ⊤<-trichotomous
     }

  ⊤-strictTotalOrder : StrictTotalOrder l0 l0 l0
  ⊤-strictTotalOrder =
    record{
      Carrier = ⊤;
      _≈_ = _≡_;
      _<_ = _⊤<_;
      isStrictTotalOrder = ⊤-IsStrictTotalOrder
     }

pointwiseRespAll : {ℓA ℓB ℓQ ℓP ℓR : Level} → {A : Set ℓA} → {B : Set ℓB} → {Q : REL A B ℓQ} → {P : A → Set ℓP} →
                   {R : B → Set ℓR} → (imp : ∀ {a b} → P a → Q a b → R b) → (lA : List A) → (lB : List B) → 
                   (AllP : LL.All P lA) → (Pointwise Q lA lB) → LL.All R lB
 
pointwiseRespAll {A = A} {B} {Q} {P} {R} imp [] [] AllP pwQ = []
pointwiseRespAll {A = A} {B} {Q} {P} {R} imp [] (hB ∷ tB) AllP ()
pointwiseRespAll {A = A} {B} {Q} {P} {R} imp (hA ∷ tA) [] AllP ()
pointwiseRespAll {A = A} {B} {Q} {P} {R} imp (hA ∷ tA) (hB ∷ tB) (hP ∷ tP) (hQ ∷ tQ) = 
  (imp hP hQ) ∷ (pointwiseRespAll imp tA tB tP tQ)

pointwiseRespAll⃖ : {ℓA ℓB ℓQ ℓP ℓR : Level} → {A : Set ℓA} → {B : Set ℓB} → {Q : REL A B ℓQ} → {P : A → Set ℓP} →
                   {R : B → Set ℓR} → (imp : ∀ {a b} → R b → Q a b → P a) → (lA : List A) → (lB : List B) → 
                   (AllP : LL.All R lB) → (Pointwise Q lA lB) → LL.All P lA
 
pointwiseRespAll⃖ {A = A} {B} {Q} {P} {R} imp [] [] AllR pwQ = []
pointwiseRespAll⃖ {A = A} {B} {Q} {P} {R} imp [] (hB ∷ tB) AllR ()
pointwiseRespAll⃖ {A = A} {B} {Q} {P} {R} imp (hA ∷ tA) [] AllR ()
pointwiseRespAll⃖ {A = A} {B} {Q} {P} {R} imp (hA ∷ tA) (hB ∷ tB) (hR ∷ tR) (hQ ∷ tQ) = 
  (imp hR hQ) ∷ (pointwiseRespAll⃖ imp tA tB tR tQ)

pointwiseRespAny : {ℓA ℓB ℓQ ℓP ℓR : Level} → {A : Set ℓA} → {B : Set ℓB} → {Q : REL A B ℓQ} → {P : A → Set ℓP} →
                   {R : B → Set ℓR} →  
                   (imp : ∀ {a b} → P a → Q a b → R b) → 
                   (lA : List A) → (lB : List B) →
                   (anyP : LA.Any P lA) → (Pointwise Q lA lB) → LA.Any R lB

pointwiseRespAny {A = A} {B} {Q} {P} {R} imp [] [] anyP pwQ = ⊥-elim $ LAP.¬Any[] anyP 
pointwiseRespAny {A = A} {B} {Q} {P} {R} imp [] (hB ∷ tB) anyP ()
pointwiseRespAny {A = A} {B} {Q} {P} {R} imp (hA ∷ tA) [] anyP ()
pointwiseRespAny {A = A} {B} {Q} {P} {R} imp (hA ∷ tA) (hB ∷ tB) (here hP) (hQ ∷ tQ) = 
  here (imp hP hQ)
pointwiseRespAny {A = A} {B = B} {Q = Q} {P = P} {R = R} imp (hA ∷ tA) (hB ∷ tB) (there tP) (hQ ∷ tQ) = 
  there $ pointwiseRespAny imp tA tB tP tQ 

pointwise∈ : {ℓA ℓB ℓQ : Level} → {A : Set ℓA} → {B : Set ℓB} →
              {Q : REL A B ℓQ} → (lA : List A) → (lB : List B) → (a : A) →
              (a ∈ lA) → (Pointwise Q lA lB) → Σ[ b ∈ B ] Q a b 
pointwise∈ {A = A} {B} {Q} lA lB a a∈lA pw = LA.satisfied $ pointwiseRespAny imp lA lB a∈lA pw 
  where
    imp : ∀ {a' b} → a ≡ a' → Q a' b → Q a b
    imp {a'} {b} eq qab rewrite PE.sym eq = qab

pointwiseRespAny⃖ : {ℓA ℓB ℓQ ℓP ℓR : Level} → {A : Set ℓA} → {B : Set ℓB} → {Q : REL A B ℓQ} → {P : A → Set ℓP} →
                   {R : B → Set ℓR} →  
                   (imp : ∀ {a b} → R b → Q a b → P a) → 
                   (lA : List A) → (lB : List B) →
                   (anyR : LA.Any R lB) → (Pointwise Q lA lB) → LA.Any P lA

pointwiseRespAny⃖ {A = A} {B} {Q} {P} {R} imp [] [] anyR pwQ = ⊥-elim $ LAP.¬Any[] anyR 
pointwiseRespAny⃖ {A = A} {B} {Q} {P} {R} imp [] (hB ∷ tB) anyR ()
pointwiseRespAny⃖ {A = A} {B} {Q} {P} {R} imp (hA ∷ tA) [] anyR ()
pointwiseRespAny⃖ {A = A} {B} {Q} {P} {R} imp (hA ∷ tA) (hB ∷ tB) (here hR) (hQ ∷ tQ) = 
  here (imp hR hQ)
pointwiseRespAny⃖ {A = A} {B = B} {Q = Q} {P = P} {R = R} imp (hA ∷ tA) (hB ∷ tB) (there tR) (hQ ∷ tQ) = 
  there $ pointwiseRespAny⃖ imp tA tB tR tQ 


pointwise∈⃖ : {ℓA ℓB ℓQ : Level} → {A : Set ℓA} → {B : Set ℓB} →
              {Q : REL A B ℓQ} → (lA : List A) → (lB : List B) → (b : B) →
              (b ∈ lB) → (Pointwise Q lA lB) → Σ[ a ∈ A ] Q a b 
pointwise∈⃖ {A = A} {B} {Q} lA lB b b∈lB pw = LA.satisfied $ pointwiseRespAny⃖ imp lA lB b∈lB pw 
  where
    imp : ∀ {a b'} → b ≡ b' → Q a b' → Q a b
    imp {a'} {b} eq qab rewrite PE.sym eq = qab


pointwise-[]ˡ : {ℓA ℓB ℓQ ℓP : Level} → {A : Set ℓA} → {B : Set ℓB} → {Q : REL B A ℓQ} → 
               {lA : List A} → Pointwise Q [] lA → lA ≡ [] 

pointwise-[]ˡ {A = A} {Q} {_} [] = PE.refl


pointwise-[]ʳ : {ℓA ℓB ℓQ : Level} → {A : Set ℓA} → {B : Set ℓB} → {Q : REL A B ℓQ} → 
                {lA : List A} → Pointwise Q lA [] → lA ≡ [] 

pointwise-[]ʳ {A = A} {Q} {_} [] = PE.refl


module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : JoinSemilattice ℓ₁ ℓ₂ ℓ₃} where
  open JoinSemilattice A renaming 
    (_≤_ to _≤A_; _∨_ to _∨A_ ; _≈_ to _≈A_ ; refl to ≤A-refl ; reflexive to ≤A-reflexive )
  
  open import Relation.Binary.Properties.JoinSemilattice A

  connecting→ : (a b : Carrier) → (a ≤A b) → (a ∨A b ≈A b)
  connecting→ a b a≤b = antisym a∨b≤b b≤a∨b
    where
      open import Relation.Binary.PartialOrderReasoning (JoinSemilattice.poset A)

      a∨b≤b : a ∨A b ≤A b
      a∨b≤b = 
        begin
          a ∨A b ≤⟨ ∨-monotonic a≤b ≤A-refl ⟩
          b ∨A b ≤⟨ ≤A-reflexive (∨-idempotent b) ⟩
          b
         ∎

      b≤a∨b : b ≤A a ∨A b
      b≤a∨b = proj₁ $ proj₂ $ supremum a b 

private
  inj-clash' : {ℓA ℓB : Level} → {A : Set ℓA} → {B : Set ℓB} → (a : A) → (b : B) → (c : A ⊎ B) → 
               (inj₁ a ≡ c) → (inj₂ b ≡ c) → ⊥
  inj-clash' a b (inj₁ x) eq1 ()
  inj-clash' a b (inj₂ y) () eq2 

inj-clash : {ℓA ℓB : Level} → {A : Set ℓA} → {B : Set ℓB} → (a : A) → (b : B) →  
            (inj₁ a ≡ inj₂ b) → ⊥

inj-clash a b eq = inj-clash' a b (inj₁ a) PE.refl (PE.sym eq)  
  
preorder→setoid : ∀ {ℓ₀ ℓ₁ ℓ₂} → (P : Preorder ℓ₀ ℓ₁ ℓ₂) → Setoid _ _
preorder→setoid P = record
  { Carrier = Preorder.Carrier P
  ; _≈_ = Preorder._≈_ P
  ; isEquivalence = Preorder.isEquivalence P
  }

poset→setoid : ∀ {ℓ₀ ℓ₁ ℓ₂} → (P : Poset ℓ₀ ℓ₁ ℓ₂) → Setoid _ _
poset→setoid P = record
  { Carrier = Poset.Carrier P
  ; _≈_ = Poset._≈_ P
  ; isEquivalence = Poset.isEquivalence P
  }

module _ {S : BoundedJoinSemilattice l0 l0 l0} where
  open import Relation.Binary.Properties.JoinSemilattice
  open import Relation.Binary.Properties.BoundedJoinSemilattice
  open BoundedJoinSemilattice S renaming 
    (_≤_ to _≤ₛ_ ; _∨_ to _∨ₛ_ ; ⊥ to ⊥ₛ ; _≈_ to _≈ₛ_ ; reflexive to reflexiveₛ ; joinSemiLattice to joinSemilatticeₛ ;
     antisym to antisymₛ ; trans to ≤ₛ-trans)
  open BoundedJoinSemilattice.Eq S renaming (refl to reflₛ ; sym to symₛ)
  ∨-resp-≈ˡ : {a b c : Carrier} → (a≈b : a ≈ₛ b) → (a ∨ₛ c ≈ₛ b ∨ₛ c)
  ∨-resp-≈ˡ {a} {b} {c} a≈b = antisymₛ a∨c≤b∨c b∨c≤a∨c
    where
      a∨c≤b∨c : a ∨ₛ c ≤ₛ b ∨ₛ c
      a∨c≤b∨c = ∨-monotonic joinSemilatticeₛ (reflexiveₛ a≈b) (reflexiveₛ reflₛ)

      b∨c≤a∨c : b ∨ₛ c ≤ₛ a ∨ₛ c
      b∨c≤a∨c = ∨-monotonic joinSemilatticeₛ (reflexiveₛ $ symₛ a≈b) (reflexiveₛ reflₛ)

  ∨-resp-≈ʳ : {a b c : Carrier} → (b≈c : b ≈ₛ c) → (a ∨ₛ b ≈ₛ a ∨ₛ c)
  ∨-resp-≈ʳ {a} {b} {c} b≈c = antisymₛ a∨b≤a∨c a∨c≤a∨b 
    where
      a∨b≤a∨c : a ∨ₛ b ≤ₛ a ∨ₛ c
      a∨b≤a∨c = ∨-monotonic joinSemilatticeₛ (reflexiveₛ reflₛ) (reflexiveₛ b≈c) 

      a∨c≤a∨b : a ∨ₛ c ≤ₛ a ∨ₛ b
      a∨c≤a∨b = ∨-monotonic joinSemilatticeₛ (reflexiveₛ reflₛ) (reflexiveₛ $ symₛ b≈c)

  ∨-list : List Carrier → Carrier
  ∨-list (c ∷ cs) = c ∨ₛ (∨-list cs)
  ∨-list [] = ⊥ₛ
  
  ∨-to-list : (a b : Carrier) → (a ∨ₛ b ≈ₛ ∨-list (a ∷ b ∷ []))
  ∨-to-list a b = ∨-resp-≈ʳ $ symₛ $ identityʳ S b
  
  ∨-list-≤-single : (s : Carrier) → (l : List Carrier) → (LA.Any (s ≤ₛ_) l) → s ≤ₛ (∨-list l)
  ∨-list-≤-single s [] s≤[] = ⊥-elim $ ¬Any[] s≤[]
  ∨-list-≤-single s (s' ∷ l') (here s≤s') = ≤ₛ-trans s≤s' (proj₁ $ supremum s' $ ∨-list l')
  ∨-list-≤-single s (s' ∷ l') (there s≤l') = ≤ₛ-trans (∨-list-≤-single s l' s≤l') (proj₁ $ proj₂ $ supremum s' (∨-list l'))
  
  ∨-list-upper : (l : List Carrier) → (LL.All (_≤ₛ (∨-list l)) l)
  ∨-list-upper [] = []
  ∨-list-upper (s ∷ l') = 
    (proj₁ $ supremum s (∨-list l')) ∷  
    LL.map (λ ·≤∨l' → ≤ₛ-trans ·≤∨l' (proj₁ $ proj₂ $ supremum s (∨-list l') )) (∨-list-upper l')  
  
  ∨-list-sup  : (l : List Carrier) → (s : Carrier) → (∨-list l ≤ₛ s) → LL.All (_≤ₛ s) l
  ∨-list-sup [] s ∨l≤s = []
  ∨-list-sup (x ∷ l') s x∨l'≤s = q ∷ (∨-list-sup l' s p)
    where
      q : x ≤ₛ s
      q = ≤ₛ-trans (proj₁ $ supremum x (∨-list l')) x∨l'≤s

      p : ∨-list l' ≤ₛ s
      p = ≤ₛ-trans (proj₁ $ proj₂ $ supremum x (∨-list l')) x∨l'≤s
  
  ∨-list-≤ : (l₁ : List Carrier) → (l₂ : List Carrier) → LL.All (λ · → LA.Any (· ≤ₛ_) l₂) l₁ → (∨-list l₁) ≤ₛ (∨-list l₂)
  ∨-list-≤ [] [] l₁≤l₂ = reflexiveₛ reflₛ
  ∨-list-≤ [] (s₂ ∷ l₂) [] = minimum (s₂ ∨ₛ ∨-list l₂)
  ∨-list-≤ (x ∷ l₁) [] (px ∷ l₁≤l₂') = ⊥-elim $ ¬Any[] px
  ∨-list-≤ (s₁ ∷ l₁) (s₂ ∷ l₂) (s₁≤s₂l₂ ∷ l₁≤s₂l₂) = 
    (proj₂ $ proj₂ $ supremum s₁ (∨-list l₁)) (s₂ ∨ₛ (∨-list l₂)) s₁≤∨s₂l₂ ∨l₁≤∨s₂l₂ 
    where
      ∨l₁≤∨s₂l₂ : ∨-list l₁ ≤ₛ s₂ ∨ₛ ∨-list l₂
      ∨l₁≤∨s₂l₂ = ∨-list-≤ l₁ (s₂ ∷ l₂) l₁≤s₂l₂

      s₁≤∨s₂l₂ : s₁ ≤ₛ (s₂ ∨ₛ ∨-list l₂)
      s₁≤∨s₂l₂ = ∨-list-≤-single s₁ (s₂ ∷ l₂) s₁≤s₂l₂

  ∨-list-pointwise-≤ : (l₁ : List Carrier) → (l₂ : List Carrier) → Pointwise _≤ₛ_ l₁ l₂ →  (∨-list l₁) ≤ₛ (∨-list l₂)
  ∨-list-pointwise-≤ [] [] [] = minimum ⊥ₛ
  ∨-list-pointwise-≤ [] (s₂ ∷ l₂) ()
  ∨-list-pointwise-≤ (s₁ ∷ l₁) [] ()
  ∨-list-pointwise-≤ (s₁ ∷ l₁) (s₂ ∷ l₂) (s₁≤s₂ ∷ l₁≤l₂) = 
    ∨-monotonic joinSemilatticeₛ s₁≤s₂ (∨-list-pointwise-≤ l₁ l₂ l₁≤l₂)


All⊥→[] : {A : Set} → {l : List A} → LL.All (Function.const ⊥) l → l ≡ []
All⊥→[] {l = []} [] = PE.refl 
All⊥→[] {l = h ∷ t} (contr ∷ rest) = ⊥-elim contr

⊥-unique : (a b : ⊥) → a ≡ b
⊥-unique () ()


{-
  ∨-list-≤← : (l₁ : List Carrier) → (l₂ : List Carrier) → (∨-list l₁) ≤ₛ (∨-list l₂) → LL.All (λ · → (· ≈ₛ ⊥ₛ) ⊎ LA.Any (· ≤ₛ_) l₂) l₁
  ∨-list-≤← [] l₂ ∨l₁≤∨l₂ = []
  ∨-list-≤← (x ∷ l₁) [] ∨l₁≤∨l₂ = {!!}
  ∨-list-≤← (x ∷ l₁) (x₁ ∷ l₂) ∨l₁≤∨l₂ = {!!}
-}
