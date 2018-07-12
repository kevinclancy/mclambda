module FinPoset where

open import Function using (_∘_ ; _$_)
open import Data.Nat as N renaming (_≤′_ to _N≤_ ; _<′_ to _N<_) hiding (_≤_ ; _≤?_)
open import Data.Nat.Properties as NP using ()
open import Data.Star as S
open import Data.Star.Properties as SP
open import Data.List as L
open import Data.List.Any as LA
open import Data.Bool as B
open import Util renaming (_≤′?_ to _N≤?_)
open import Relation.Binary.PropositionalEquality as PE
open import Relation.Binary as RB
open import Relation.Unary as RU
open import Relation.Nullary as RN
open import Data.Product
open import Level renaming (zero to ℓ₀)
open import Data.Empty
open import Induction.WellFounded as WF

-- we may want to show that a transitive property of the covers relation
-- is also present in ≤, in which case Data.Star.Properties' fold-◅◅ theorem may be useful 

record Cover (A : Set) (depth : A → ℕ) : Set where
  inductive
  constructor _/_/_
  field
    -- a poset element that is covered by hi
    lo : A
    -- a poset element that covers lo
    hi : A
    -- a proof that lo is "deeper" in the Hasse diagram than hi 
    belowDeeper : (depth hi) N.<′ (depth lo) 

module FinPoset 
    (A : Set) 
    (depth : A → ℕ) 
    (covers : List $ Cover A depth)
    (_A=_ : RB.Decidable (_≡_ {A = A}))
 where
    private
     CoverMatches : (A₀ A₁ : A) → Pred (Cover A depth) ℓ₀
     CoverMatches A₀ A₁ = (λ cov → (Cover.lo cov ≡ A₀) × (Cover.hi cov ≡ A₁))
    
    -- Cover relation generated from covers
    -- TODO: prove this is well-founded
    _≺_ : Rel A ℓ₀
    A₀ ≺ A₁ = Any (CoverMatches A₀ A₁) covers
    
    private 
      ≺-decr : (A₀ A₁ : A) → (A₀ ≺ A₁) → (depth A₁ N.<′ depth A₀)
      ≺-decr A₀ A₁ A₀≺A₁ = ≺-decr-aux covers A₀ A₁ A₀≺A₁
        where
          ≺-decr-aux : (l : List $ Cover A depth) → (A₀ A₁ : A) → (Any (CoverMatches A₀ A₁) l) → (depth A₁ N.<′ depth A₀) 
          ≺-decr-aux l A₀ A₁ (here {x} (refl , refl)) = Cover.belowDeeper x
          ≺-decr-aux (x ∷ xs)  A₀ A₁ (there A₀≺A₁) = ≺-decr-aux xs A₀ A₁ A₀≺A₁ 
    
    _≤_ : Rel A ℓ₀
    _≤_ = Star _≺_
    
    private
      ≤-decr : (A₀ A₁ : A) → (A₀ ≤ A₁) → (depth A₁ N.≤′ depth A₀)
      ≤-decr A₀ .A₀ ε = ≤′-refl
      ≤-decr A₀ A₁ (_◅_ {j = A₂} A₀≺A₂  A₂≤A₁) = NP.≤⇒≤′ p₁ 
        where
          open NP.≤-Reasoning
          p₀ : (depth A₂) N.<′ (depth A₀)
          p₀ = ≺-decr A₀ A₂ A₀≺A₂

          p₁ : (depth A₁) N.≤ (depth A₀)
          p₁ = begin
            (depth A₁) ≤⟨ NP.≤′⇒≤ (≤-decr A₂ A₁ A₂≤A₁) ⟩
            (depth A₂) ≤⟨ NP.≤′⇒≤ (≤′-step ≤′-refl) ⟩
            (N.suc $ depth A₂) ≤⟨ NP.≤′⇒≤ p₀ ⟩
            (depth A₀)
           ∎

    ≤-preorder : Preorder _ _ _
    ≤-preorder = SP.preorder _≺_

    ≤-isPreorder : IsPreorder _≡_ _≤_
    ≤-isPreorder = Preorder.isPreorder ≤-preorder
    
    private
      ≤-isAntisymmetric : Antisymmetric _≡_ _≤_
      ≤-isAntisymmetric {x} {.x} ε y≤x = refl
      ≤-isAntisymmetric {x} {.x} x≤y ε = refl
      ≤-isAntisymmetric {x} {y} (_◅_ {j = j1} x≺j1 j1≤y) (_◅_ {j = j2} y≺j2 j2≤x) = ⊥-elim contr
        where 
          open NP.≤-Reasoning
          dy<dx : (depth y) N.< (depth x)
          dy<dx = begin
            (N.suc $ depth y) ≤⟨ s≤s $ NP.≤′⇒≤ (≤-decr j1 y j1≤y) ⟩
            (N.suc $ depth j1) ≤⟨ NP.≤′⇒≤ (≺-decr x j1 x≺j1) ⟩ 
            (depth x)
           ∎

          dx<dy : (depth x) N.< (depth y)
          dx<dy = begin
            (N.suc $ depth x) ≤⟨ s≤s $ NP.≤′⇒≤ (≤-decr j2 x j2≤x) ⟩
            (N.suc $ depth j2) ≤⟨ NP.≤′⇒≤ (≺-decr y j2 y≺j2) ⟩ 
            (depth y)
           ∎
         
          contr : ⊥ 
          contr with (NP.<-cmp (depth x) (depth y))
          contr | tri< _ _ ¬dy<dx = ¬dy<dx dy<dx
          contr | tri≈ ¬dx<dy _ _ = ¬dx<dy dx<dy
          contr | tri> ¬dx<dy _ _ = ¬dx<dy dx<dy
          
    ≤-isPartialOrder : IsPartialOrder _≡_ _≤_
    ≤-isPartialOrder = record{ isPreorder = ≤-isPreorder ; antisym = ≤-isAntisymmetric }

    ≤-poset : Poset l0 l0 l0
    ≤-poset = 
      record{
        Carrier = A;
        _≈_ = _≡_;
        _≤_ = _≤_;
        isPartialOrder = ≤-isPartialOrder
       }

    private
     PathThrough :  (A₀ A₁ : A) → Pred (Cover A depth) ℓ₀
     PathThrough A₀ A₁ = (λ cov → (A₀ ≡ Cover.lo cov) × (Cover.hi cov ≤ A₁) )

    private
     mutual
      ≤?-bounded : (d : ℕ) → (a : WF.Acc _N<_ d) → (A₀ A₁ : A) → 
                  (A₀<d : depth A₀ N< d) → Dec (A₀ ≤ A₁)

      ≤?-bounded d a A₀ A₁ A₀<d with (A₀ A= A₁)
      ≤?-bounded d a A₀ A₁ A₀<d | yes A₀≡A₁ rewrite A₀≡A₁ = yes ε
      ≤?-bounded d a A₀ A₁ A₀<d | no ¬A₀≡A₁ with (LA.any (pathThrough d a A₀ A₁ A₀<d) covers)
      ≤?-bounded d a A₀ A₁ A₀<d | no ¬A₀≡A₁ | yes anyThrough = 
        yes $ anyEliminate covers eliminator anyThrough
        where 
          eliminator : AnyEliminator (Cover A depth) (A₀ ≤ A₁) (PathThrough A₀ A₁) covers
          eliminator cov f (A₀≡lo , hi≤A₁) cov∈covers = A₀≺hi ◅ hi≤A₁
            where
              A₀≺hi : A₀ ≺ Cover.hi cov
              A₀≺hi = f (CoverMatches A₀ (Cover.hi cov)) (sym A₀≡lo , refl)
      ≤?-bounded d a A₀ A₁ A₀<d | no ¬A₀≡A₁ | no ¬anyThrough = no contr
        where
          contr : A₀ ≤ A₁ → ⊥
          contr ε = ¬A₀≡A₁ refl
          contr (_◅_ {j = B} A₀≺B B≤A₁) = ¬anyThrough $ anyEliminate covers eliminator A₀≺B
            where
              eliminator : AnyEliminator (Cover A depth) (LA.Any (PathThrough A₀ A₁) covers) (CoverMatches A₀ B) covers
              eliminator cov f (lo≡A₀ , hi≡B) cov∈covers = f (PathThrough A₀ A₁) (sym lo≡A₀ , hi≤A₁)
                where
                  hi≤A₁ : Cover.hi cov ≤ A₁
                  hi≤A₁ rewrite hi≡B = B≤A₁

      pathThrough : (d : ℕ) → (a : WF.Acc _N<_ d) → (A₀ A₁ : A) → 
                   (A₀<d : depth A₀ N< d) → RU.Decidable (PathThrough A₀ A₁)

      pathThrough d (acc rs) A₀ A₁ A₀<d (lo / hi / hi<lo) with (A₀ A= lo)
      pathThrough d (acc rs) A₀ A₁ A₀<d (lo / hi / hi<lo) | yes refl
          with (≤?-bounded (depth lo) (rs (depth lo) A₀<d) hi A₁ hi<lo)
          where 
            accLo : WF.Acc _N<_ (depth lo)
            accLo = rs (depth lo) A₀<d
      pathThrough d (acc rs) A₀ A₁ A₀<d (lo / hi / hi<lo) | yes refl | yes hi≤A₁ =  yes (refl , hi≤A₁)
      pathThrough d (acc rs) A₀ A₁ A₀<d (lo / hi / hi<lo) | yes refl | no ¬hi≤A₁ = no contr
        where
          contr : PathThrough A₀ A₁ (lo / hi / hi<lo) → ⊥
          contr (_ , hi≤A₁) = ¬hi≤A₁ hi≤A₁
      pathThrough d (acc rs) A₀ A₁ A₀<d (lo / hi / hi<lo) | no ¬A₀≡lo = no contr
        where
          contr : PathThrough A₀ A₁ (lo / hi / hi<lo) → ⊥
          contr (A₀≡lo , _) = ¬A₀≡lo A₀≡lo
     --end mutual
    --end private
    
    -- A decision procedure for _≤_, the partial order derived from the provided cover list
    _≤?_ : RB.Decidable _≤_
    A₀ ≤? A₁ = ≤?-bounded d (<′-well-founded d) A₀ A₁ ≤′-refl 
      where
        open import Induction.Nat using (<′-well-founded)
        d : ℕ 
        d = N.suc (depth A₀)
        
        
