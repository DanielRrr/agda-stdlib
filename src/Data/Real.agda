module Data.Real where

open import Data.Sum
open import Data.Rational as ℚ using (ℚ; -_ ; _*_; _÷suc_; _-_; _+_; ∣_∣; decTotalOrder; _≤_; *≤* ; _≤?_; _÷_)
open import Data.Rational.Properties using (ℚ-swap; ℚabs₂; +-red₂; ℚtriang; _ℚ+-mono_; ℚ≤lem; _⁻¹)
open import Data.Integer as ℤ using (ℤ; +_ ; -[1+_])
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Binary.Core using (Rel; IsEquivalence)
import Level
open import Relation.Binary using (IsPreorder; Preorder; IsPartialOrder; DecTotalOrder; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; subst; cong; cong₂)
open import Data.Product


--Constructible Real numbers as described by Bishop in Grundlehren der mathematischen Wissenshaften (1967)

--A real number is defined to be a sequence along 
--with a proof that the sequence is regular
record ℝ : Set where
  constructor Real
  field
    f : ℕ -> ℚ
    reg : {n m : ℕ} -> ∣ f n ℚ.- f m ∣ ℚ.≤ (suc n)⁻¹ ℚ.+ (suc n)⁻¹

------------------------------------------------------------------------
-- Equality of real numbers.

infix 4 _≃_

_≃_ : Rel ℝ Level.zero
x ≃ y =  {n : ℕ} -> ∣ ℝ.f x n - ℝ.f y n ∣ ≤ (suc n)⁻¹ ℚ.+ (suc n)⁻¹

-- Proof that this is an equivalence relation-------------------

isEquivalence : IsEquivalence _≃_
isEquivalence = record {
  refl = λ {x} -> refl≃ {x} ;
  sym = λ {x}{y} -> sym≃ {x}{y};
  trans = λ {a}{b}{c} -> trans≃ {a}{b}{c}
  }
  where

  --reflexitivity
  refl≃ : {x : ℝ} -> (x ≃ x)
  refl≃ {(Real f reg)} = reg

  --symmetry
  sym≃ : {x y : ℝ} -> (x ≃ y -> y ≃ x)
  sym≃ {x}{y} xy = λ {n} -> (subst (λ a -> a ≤ (suc n)⁻¹ ℚ.+ (suc n)⁻¹) (ℚabs₂ (ℝ.f x n) (ℝ.f y n))) (xy {n})

  --transitivity
  postulate Bishopslem : {x y : ℝ} -> ({j n : ℕ} -> ∃ λ Nⱼ -> (∣ ℝ.f x (Nⱼ ℕ.+ n) - ℝ.f y (Nⱼ ℕ.+ n) ∣ ≤ ((+ 1) ÷suc j))) → (x ≃ y)

  trans≃ : {x y z : ℝ} -> (x ≃ y) -> (y ≃ z) -> (x ≃ z)
  trans≃ {x}{y}{z} xy yz = Bishopslem {x}{z} (λ {j}{n} -> 
    Nⱼ {j} , (≤trans 
      (ℚtriang (ℝ.f x (Nⱼ {j} ℕ.+ n)) (ℝ.f y (Nⱼ {j} ℕ.+ n)) (ℝ.f z (Nⱼ {j} ℕ.+ n))) 
      (≤trans 
        ((xy {Nⱼ {j} ℕ.+ n}) ℚ+-mono (yz {Nⱼ {j} ℕ.+ n})) 
        (≤trans 
          (((ℚ≤lem {Nⱼ {j}} {n}) ℚ+-mono (ℚ≤lem {Nⱼ {j}} {n})) ℚ+-mono (((ℚ≤lem {Nⱼ {j}} {n}) ℚ+-mono (ℚ≤lem {Nⱼ {j}} {n}))))
          (≈->≤ (+-red₂ j) )))))
    where
      ≈->≤ = IsPreorder.reflexive (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (DecTotalOrder.isDecTotalOrder ℚ.decTotalOrder))))
      ≤trans = DecTotalOrder.trans  ℚ.decTotalOrder
      Nⱼ = λ {j} -> suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j))))
