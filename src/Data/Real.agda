module Data.Real where

open import Data.Sum
open import Data.Rational as ℚ using (ℚ; -_ ; _*_; _÷suc_; _-_; _+_; ∣_∣; decTotalOrder; _≤_; *≤* ; _≤?_; _÷_)
open import Data.Rational.Properties using (ℚ-swap; ℚabs₂; +-red₂; ℚtriang; _ℚ+-mono_; ℚ≤lem)
open import Data.Integer as ℤ using (ℤ; +_ ; -[1+_]) renaming (_-_ to ℤ_-_; _+_ to _ℤ+_; _*_ to  _ℤ*_;_≤_ to ℤ_≤_)
open import Data.Nat as ℕ using (ℕ; suc; zero; compare; z≤n; _+⋎_; pred) renaming (_≤_ to ℕ_≤_)
open import Relation.Binary.Core using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core using (trans; subst)
import Level
open import Relation.Binary using (IsPreorder; Preorder; IsPartialOrder; DecTotalOrder; IsTotalOrder; IsDecTotalOrder)
open import Algebra using (module CommutativeRing; Ring; module CommutativeMonoid; module AbelianGroup)
open import Data.Integer.Properties using (commutativeRing; abs-◃)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; subst; cong; cong₂)
open import Data.Product


--Constructible Real numbers as described by Bishop

--Constructs a real number given a sequence approximating it and a proof that it is regular
record ℝ : Set where
  constructor Real
  field
    f : ℕ -> ℚ
    reg : {n m : ℕ} -> (∣ f n ℚ.- f m ∣) ℚ.≤ (+ 1) ÷suc n ℚ.+ (+ 1) ÷suc m

------------------------------------------------------------------------
-- Equality of real numbers.

infix 4 _≃_

_≃_ : Rel ℝ Level.zero
x ≃ y =  {n : ℕ} -> ∣ ℝ.f x n - ℝ.f y n ∣ ≤ (+ 1) ÷suc n ℚ.+ (+ 1) ÷suc n

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
  sym≃ {x}{y} xy = λ {n} -> (subst (λ a -> a ≤ (+ 1) ÷suc n ℚ.+ (+ 1) ÷suc n) (ℚabs₂ (ℝ.f x n) (ℝ.f y n))) (xy {n})

  --transitivity
  --The following lemma, which gives us another way to formulate equality, is a formalized version of Lemma 2.3 in Bishop's Grundlehren der mathematischen Wissenshaften, 1967
  {-
  postulate Bishopslem : {x y : ℝ} -> ({j : ℕ} -> ∃ λ Nⱼ -> (∣ ℝ.f x Nⱼ - ℝ.f y Nⱼ ∣ ≤ ((+ 1) ÷suc j))) → (x ≃ y)

  trans≃ : {x y z : ℝ} -> (x ≃ y) -> (y ≃ z) -> (x ≃ z)
  trans≃ {x}{y}{z} xy yz = Bishopslem {x}{z} (λ {j} -> ((suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j))))) , (DecTotalOrder.trans  ℚ.decTotalOrder (ℚtriang (ℝ.f x (suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j)))))) (ℝ.f y (suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j)))))) (ℝ.f z (suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j))))))) (DecTotalOrder.trans  ℚ.decTotalOrder ((xy {(suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j)))))}) +-mono (yz {(suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j)))))})) ((IsPreorder.reflexive (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (DecTotalOrder.isDecTotalOrder ℚ.decTotalOrder)))) (+-red₂ j)))) )))
-}
  postulate Bishopslem : {x y : ℝ} -> ({j n : ℕ} -> ∃ λ Nⱼ -> (∣ ℝ.f x (Nⱼ ℕ.+ n) - ℝ.f y (Nⱼ ℕ.+ n) ∣ ≤ ((+ 1) ÷suc j))) → (x ≃ y)

  trans≃ : {x y z : ℝ} -> (x ≃ y) -> (y ≃ z) -> (x ≃ z)
  trans≃ {x}{y}{z} xy yz = Bishopslem {x}{z} (λ {j}{n} -> ((suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j))))) , (DecTotalOrder.trans  ℚ.decTotalOrder (ℚtriang (ℝ.f x (suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j)))) ℕ.+ n)) (ℝ.f y (suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j)))) ℕ.+ n)) (ℝ.f z (suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j)))) ℕ.+ n))) (DecTotalOrder.trans  ℚ.decTotalOrder ((xy {(suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j)))) ℕ.+ n)}) ℚ+-mono (yz {(suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j)))) ℕ.+ n)})) (DecTotalOrder.trans ℚ.decTotalOrder (((ℚ≤lem {suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j))))} {n}) ℚ+-mono (ℚ≤lem {suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j))))} {n})) ℚ+-mono (((ℚ≤lem {suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j))))} {n}) ℚ+-mono (ℚ≤lem {suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j))))} {n})))) ((IsPreorder.reflexive (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (DecTotalOrder.isDecTotalOrder ℚ.decTotalOrder)))) (+-red₂ j)))) ))))
