{- 

Scalar functors on posets (for capsule types). 

-}

module PosetScalars where

open import Scalars
open import SemScalars
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Data.Product

open import Util

data q' : Set where
  qAny' : q'
  qMono' : q'
  qAnti' : q'

q'→q : q' → q
q'→q qAny' = qAny 
q'→q qMono' = qMono
q'→q qAnti' = qAnti

⟦_q'⟧ : q' → Poset l0 l0 l0 → Poset l0 l0 l0
⟦ qAny' q'⟧ P = record
  { Carrier = Carrier
  ; _≈_ = _≈_
  ; _≤_ = Preorder._∼_ qP'
  ; isPartialOrder = record
    { isPreorder = Preorder.isPreorder qP' -- Preorder.isPreorder (⟦ qAny q⟧ preorder) 
    ; antisym = antisym'
    }
  }
  where
    open Poset P
    P' = preorder
    qP' = ⟦ qAny q⟧ P'

    antisym' : Antisymmetric (Preorder._≈_ qP') (Preorder._∼_ qP')
    antisym' (x≤y , _) (y≤x , _) = antisym x≤y y≤x
⟦ qMono' q'⟧ P = P
⟦ qAnti' q'⟧ P = record
    { Carrier = Carrier
    ; _≈_ = _≈_
    ; _≤_ = Preorder._∼_ qP'
    ; isPartialOrder = record
      { isPreorder = Preorder.isPreorder qP' -- Preorder.isPreorder (⟦ qAny q⟧ preorder) 
      ; antisym = antisym'
      }
    }
    where
      open Poset P
      P' = preorder
      qP' = ⟦ qAnti q⟧ P'

      antisym' : Antisymmetric (Preorder._≈_ qP') (Preorder._∼_ qP')
      antisym' y≤x x≤y = antisym x≤y y≤x

coheres : (P : Poset l0 l0 l0) → (q₀' : q') → (Poset.preorder (⟦ q₀' q'⟧ P) ≡ ⟦ q'→q q₀' q⟧ (Poset.preorder P))
coheres P qAny' = PE.refl
coheres P qMono' = PE.refl
coheres P qAnti' = PE.refl


