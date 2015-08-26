module Data.Real where

open import Data.Sum
open import Data.Rational as ℚ using (ℚ; -_ ; _*_; _÷suc_; 
  _-_; _+_; ∣_∣;  decTotalOrder; _≤_; *≤* ; _≤?_; _÷_; ≡⇒≃)
open import Data.Rational.Properties using (ℚ-swap; ℚabs₂; 
  +-red₂; triang; _ℚ+-mono_; ℚ≤lem; _⁻¹; lim; ℚ≤-abs₁; ℚ≤-abs₂)
open import Data.Integer as ℤ using (ℤ; +_ ; -[1+_])
open import Data.Nat as ℕ using (ℕ; suc; zero; _≤?_)
open import Data.Nat.Properties.Simple using (+-right-identity)
open import Relation.Binary.Core using (Rel; IsEquivalence)
import Level
open import Relation.Nullary.Core
open import Relation.Binary using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality as P using 
  (_≡_; refl; subst; cong; cong₂)
open import Data.Product
import Relation.Binary.PreorderReasoning as Pre

--Constructible Real numbers as described by Bishop
--A real number is defined to be a sequence along 
--with a proof that the sequence is regular
record ℝ : Set where
  constructor Real
  field
    f : ℕ -> ℚ
    reg : {n m : ℕ} -> ∣ f n - f m ∣ ≤ (suc n)⁻¹ + (suc m)⁻¹

------------------------------------------------------------------------
-- Equality of real numbers.
infix 4 _≃_

_≃_ : Rel ℝ Level.zero
x ≃ y =  {n : ℕ} -> ∣ ℝ.f x n - ℝ.f y n ∣ ≤ (suc n)⁻¹ + (suc n)⁻¹

-- Proof that this is an equivalence relation-------------------

--This lemma ((2.3) in Constructive Analysis) gives us a
--useful way to show equality
postulate Bishopslem : {x y : ℝ} -> 
           ({j : ℕ} -> ∃ λ Nⱼ -> ({m : ℕ} -> 
           ∣ ℝ.f x (Nⱼ ℕ.+ m) - ℝ.f y (Nⱼ ℕ.+ m) ∣ ≤ (suc j)⁻¹)) 
           -> (x ≃ y)

--This lemma ((2.3) in Constructive Analysis) gives us a
--useful way to show equality
bishopslem : {x y : ℝ}{m : ℕ} -> 
           ({j : ℕ} -> (∃ λ Nⱼ -> ({m : ℕ} -> 
           ∣ ℝ.f x (Nⱼ ℕ.+ m) - ℝ.f y (Nⱼ ℕ.+ m) ∣ ≤ (suc j)⁻¹)))
           -> ({n : ℕ} -> ∣ ℝ.f x n - ℝ.f y n ∣ ≤ (suc n)⁻¹ ℚ.+ (suc n)⁻¹)
bishopslem {x}{y}{m} f  = λ {n} -> begin
  ∣ ℝ.f x n - ℝ.f y n ∣ ∼⟨ triang (ℝ.f x n) (ℝ.f x m) (ℝ.f y n) ⟩
  ∣ ℝ.f x n - ℝ.f x m ∣ + ∣ ℝ.f x m - ℝ.f y n ∣ ∼⟨  ≈->≤ {∣ ℝ.f x n - ℝ.f x m ∣}{∣ ℝ.f x n - ℝ.f x m ∣} refl ℚ+-mono  triang (ℝ.f x m) (ℝ.f y m) (ℝ.f y n)   ⟩
  ∣ ℝ.f x n - ℝ.f x m ∣ + (∣ ℝ.f x m - ℝ.f y m ∣ + ∣ ℝ.f y m - ℝ.f y n ∣) ∼⟨ {!!} {-ℝ.reg x {n}{m} ℚ+-mono (proj₂ f ℚ+-mono ℝ.reg y {m}{n}) -} ⟩
  suc n ⁻¹ + suc m ⁻¹ + (suc m ⁻¹ + (suc m ⁻¹ + suc n ⁻¹)) ∼⟨ (≈->≤ {suc n ⁻¹}{suc n ⁻¹} refl ℚ+-mono lim (suc m ⁻¹) ( {!!})) ℚ+-mono (lim (suc m ⁻¹) ({!!}) ℚ+-mono (lim (suc m ⁻¹) ( {!!}) ℚ+-mono ≈->≤ {suc n ⁻¹}{suc n ⁻¹} refl)) ⟩
  suc n ⁻¹ + 0' + (0' + (0' + suc n ⁻¹)) ∼⟨ {!!} ⟩
  suc n ⁻¹ + suc n ⁻¹ ∎
  where
      open DecTotalOrder ℚ.decTotalOrder using () 
        renaming (reflexive to ≈->≤; trans to ≤trans; isPreorder to ℚisPreorder)
      --j : ℕ
      --Nⱼ = proj₁ f
      --m = λ {m} -> m
      --j = λ {j} -> j
      --m = Nⱼ ℕ.+ j
      0' = (+ 0)÷suc 0
      open Pre record {isPreorder = ℚisPreorder}

isEquivalence : IsEquivalence _≃_
isEquivalence = record {
  refl = λ {x} -> refl≃ {x} ;
  sym = λ {x}{y} -> sym≃ {x}{y};
  trans = λ {a}{b}{c} -> trans≃ {a}{b}{c}
  }
  where

  --reflexitivity
  refl≃ : {x : ℝ} -> (x ≃ x)
  refl≃ {x} = ℝ.reg x

  --symmetry
  sym≃ : {x y : ℝ} -> (x ≃ y -> y ≃ x)
  sym≃ {x}{y} x≃y = λ {n} -> 
    subst (λ a -> a ≤ (suc n)⁻¹ ℚ.+ (suc n)⁻¹) 
    (ℚabs₂ (ℝ.f x n) (ℝ.f y n)) (x≃y {n})

  --transitivity
  trans≃ : {x y z : ℝ} -> (x ≃ y) -> (y ≃ z) -> (x ≃ z)
  trans≃ {x}{y}{z} x≃y y≃z = Bishopslem {x}{z} (λ {j} -> 
    Nⱼ {j} , λ {n} -> (begin 
    ∣ ℝ.f x (Nⱼ {j} ℕ.+ n) - ℝ.f z (Nⱼ {j} ℕ.+ n) ∣ 
      ∼⟨ triang (ℝ.f x (Nⱼ {j} ℕ.+ n)) (ℝ.f y (Nⱼ {j} ℕ.+ n)) (ℝ.f z (Nⱼ {j} ℕ.+ n)) ⟩
    ∣ ℝ.f x (Nⱼ {j} ℕ.+ n) - ℝ.f y (Nⱼ {j} ℕ.+ n) ∣ + 
    ∣ ℝ.f y (Nⱼ {j} ℕ.+ n) - ℝ.f z (Nⱼ {j} ℕ.+ n) ∣
    ∼⟨ (x≃y {Nⱼ {j} ℕ.+ n}) ℚ+-mono (y≃z {Nⱼ {j} ℕ.+ n}) ⟩ 
    ((suc (Nⱼ {j} ℕ.+ n))⁻¹ ℚ.+ (suc (Nⱼ {j} ℕ.+ n))⁻¹) ℚ.+ 
    ((suc (Nⱼ {j} ℕ.+ n))⁻¹ ℚ.+ (suc (Nⱼ {j} ℕ.+ n))⁻¹)
    ∼⟨ ((ℚ≤lem {Nⱼ {j}} {n}) ℚ+-mono (ℚ≤lem {Nⱼ {j}} {n})) 
           ℚ+-mono 
         ((ℚ≤lem {Nⱼ {j}} {n}) ℚ+-mono (ℚ≤lem {Nⱼ {j}} {n})) ⟩ 
    ((suc (Nⱼ {j}))⁻¹ ℚ.+ (suc (Nⱼ {j}))⁻¹) ℚ.+ 
    ((suc (Nⱼ {j}))⁻¹ ℚ.+ (suc (Nⱼ {j}))⁻¹) 
    ∼⟨ ≈->≤ (+-red₂ j) ⟩ 
    ((suc j)⁻¹ ∎) ))
    where
      open DecTotalOrder ℚ.decTotalOrder using () 
        renaming (reflexive to ≈->≤; trans to ≤trans; isPreorder to ℚisPreorder)
      open Pre record {isPreorder = ℚisPreorder}
      Nⱼ = λ {j} -> suc ((suc (j ℕ.+ j) ℕ.+ (suc (j ℕ.+ j))))

--Examples
sqrt2 : ℝ
sqrt2 = Real f reg
  where
    f : ℕ -> ℚ
    f zero = (+ 1) ÷suc 0
    f (suc n) = ((ℚ.numerator (f n) ℤ.+ (+ 2) ℤ.* ℚ.denominator (f n)) ÷suc (ℤ.∣ ℚ.numerator (f n) ∣ ℕ.+ ℚ.denominator-1 (f n)))
    reg : {n m : ℕ} -> ∣ f n ℚ.- f m ∣ ℚ.≤ (suc n)⁻¹ ℚ.+ (suc m)⁻¹
    reg {n} {m} with n ℕ.≤? m
    reg | yes p = {!!}
    reg | no ¬p = {!!}
      where
      open DecTotalOrder ℚ.decTotalOrder using () 
        renaming (reflexive to ≈->≤; trans to ≤trans; isPreorder to ℚisPreorder)
      open Pre record {isPreorder = ℚisPreorder}
      dimin : {n : ℕ} -> ∣ f n ℚ.- f (suc (suc n)) ∣ ≤ ∣ f n ℚ.- f (suc n) ∣
      dimin {n} with f n ℚ.≤? f (suc (suc n))
      dimin | p = {!!}
       
