module Data.Real where

open import Data.Empty
open import Data.Sum
open import Relation.Binary.Core
open import Function
open import Data.Rational as ℚ using (ℚ; -_ ; _*_; _÷suc_; 
  _-_; _+_; ∣_∣;  decTotalOrder; _≤_; *≤* ; _≤?_; _÷_; ≡⇒≃)
   renaming (isEquivalence to ℚisEquivalence)
open import Data.Rational.Properties using (ℚ-swap; ℚabs₂; 
  +-red₂; triang; _ℚ+-mono_; ℚ≤lem; _⁻¹; lim; ℚ≤-abs₁; ℚ≤-abs₂;
  _ℚ<_; ℚ≤lem₂; ℚ+-comm; ℚ+-assoc; ℚ≰⇒>; <⇒≤)
open import Data.Integer as ℤ using (ℤ; +_ ; -[1+_]; ◃-left-inverse)
open import Data.Nat as ℕ using (ℕ; suc; zero; _≤?_)
open import Data.Nat.Properties.Simple using (+-right-identity; +-comm)
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


--To test if the principle is right i'm just gonna use ≤ for now
lemeronia : {p q : ℚ} -> ((p ≤ q) -> ⊥) -> ∃ λ e -> ((p ≤ q + (suc e) ⁻¹) -> ⊥)
lemeronia { -[1+ n ] ÷suc d} { -[1+ n₁ ] ÷suc d₁} ¬p = {!(_ , ())!}
lemeronia { -[1+ n ] ÷suc d} {(+ n₁) ÷suc d₁} ¬p = {!!}
lemeronia {(+ n) ÷suc d} { -[1+ n₁ ] ÷suc d₁} ¬p = {!!}
lemeronia {(+ n) ÷suc d} {(+ n₁) ÷suc d₁} ¬p = {!!}

--This lemma ((2.3) in Constructive Analysis) gives us a
--useful way to show equality
bishopslem : {x y : ℝ} -> 
           ({j : ℕ} -> (∃ λ Nⱼ -> {m : ℕ} -> 
           ∣ ℝ.f x (Nⱼ ℕ.+ m) - ℝ.f y (Nⱼ ℕ.+ m) ∣ ≤ (suc j)⁻¹))
           -> ({n : ℕ} -> ∣ ℝ.f x n - ℝ.f y n ∣ ≤ (suc n)⁻¹ ℚ.+ (suc n)⁻¹)
bishopslem {x}{y} f  {n} with ∣ ℝ.f x n - ℝ.f y n ∣ ℚ.≤? (suc n)⁻¹ ℚ.+ (suc n)⁻¹
bishopslem {x}{y} f | yes p = p
bishopslem {x}{y} f {n} | no ¬p  = ⊥-elim (proj₂ (lemeronia ¬p) prof)
  where
    e/3 = (proj₁ (lemeronia {∣ ℝ.f x n - ℝ.f y n ∣}{(suc n)⁻¹ ℚ.+ (suc n)⁻¹} ¬p))
    m' =  (proj₁ (f {e/3})) ℕ.+ e/3
    e = (suc e/3)⁻¹ + ((suc e/3)⁻¹ + (suc e/3)⁻¹ )
    prof : ∣ ℝ.f x n - ℝ.f y n ∣ ≤ (suc n)⁻¹ ℚ.+ (suc n)⁻¹ + e
    prof = begin ∣ ℝ.f x n - ℝ.f y n ∣ ∼⟨ triang (ℝ.f x n) (ℝ.f x m') (ℝ.f y n) ⟩
      ∣ ℝ.f x n - ℝ.f x m' ∣ + ∣ ℝ.f x m' - ℝ.f y n ∣ ∼⟨  ≈->≤ {∣ ℝ.f x n - ℝ.f x m' ∣}{∣ ℝ.f x n - ℝ.f x m' ∣} refl ℚ+-mono  triang (ℝ.f x m') (ℝ.f y m') (ℝ.f y n)   ⟩
      ∣ ℝ.f x n - ℝ.f x m' ∣ + (∣ ℝ.f x m' - ℝ.f y m' ∣ + ∣ ℝ.f y m' - ℝ.f y n ∣) ∼⟨  ℝ.reg x {n}{m'} ℚ+-mono ((proj₂ (f {e/3})) ℚ+-mono ℝ.reg y {m'}{n})  ⟩
      suc n ⁻¹ + suc m' ⁻¹ + (suc e/3 ⁻¹ + (suc m' ⁻¹ + suc n ⁻¹)) ∼⟨ ≈->≤ {suc n ⁻¹ + suc m' ⁻¹}{suc n ⁻¹ + suc m' ⁻¹} refl ℚ+-mono (≈->≤ {suc e/3 ⁻¹}{suc e/3 ⁻¹} refl ℚ+-mono ≈->≤ {suc m' ⁻¹ + suc n ⁻¹}{suc n ⁻¹ + suc m' ⁻¹ } (ℚ+-comm (suc m' ⁻¹) (suc n ⁻¹)) ) ⟩
      suc n ⁻¹ + suc m' ⁻¹ + (suc e/3 ⁻¹ + (suc n ⁻¹ + suc m' ⁻¹)) ∼⟨ ≈->≤ {suc n ⁻¹ + suc m' ⁻¹}{suc n ⁻¹ + suc m' ⁻¹} refl ℚ+-mono (≈->≤ {(suc e/3 ⁻¹ + (suc n ⁻¹ + suc m' ⁻¹))}{(suc e/3 ⁻¹ + suc n ⁻¹ + suc m' ⁻¹)} (ℚsym {(suc e/3 ⁻¹ + suc n ⁻¹ + suc m' ⁻¹)}{(suc e/3 ⁻¹ + (suc n ⁻¹ + suc m' ⁻¹))}(ℚ+-assoc (suc e/3 ⁻¹) (suc n ⁻¹) (suc m' ⁻¹)))) ⟩
      suc n ⁻¹ + suc m' ⁻¹ + (suc e/3 ⁻¹ + suc n ⁻¹ + suc m' ⁻¹) ∼⟨ ≈->≤ {suc n ⁻¹ + suc m' ⁻¹}{suc n ⁻¹ + suc m' ⁻¹} refl ℚ+-mono ((≈->≤ {suc e/3 ⁻¹ + suc n ⁻¹}{suc n ⁻¹ + suc e/3 ⁻¹}(ℚ+-comm (suc e/3 ⁻¹) (suc n ⁻¹)) ℚ+-mono ≈->≤ {suc m' ⁻¹}{suc m' ⁻¹} refl)) ⟩
      suc n ⁻¹ + suc m' ⁻¹ + (suc n ⁻¹ + suc e/3 ⁻¹ + suc m' ⁻¹) ∼⟨ {!!} ⟩
      suc n ⁻¹ + (suc m' ⁻¹ + (suc n ⁻¹ + suc e/3 ⁻¹ + suc m' ⁻¹)) ∼⟨ {!!} ⟩
      suc n ⁻¹ + (suc m' ⁻¹ + (suc n ⁻¹ + (suc e/3 ⁻¹ + suc m' ⁻¹))) ∼⟨ {!!} ⟩
      suc n ⁻¹ + (suc m' ⁻¹ + suc n ⁻¹ + (suc e/3 ⁻¹ + suc m' ⁻¹)) ∼⟨ {!!} ⟩
      suc n ⁻¹ + (suc n ⁻¹ + suc m' ⁻¹ + (suc e/3 ⁻¹ + suc m' ⁻¹)) ∼⟨ {!!} ⟩
      suc n ⁻¹ + (suc n ⁻¹ + (suc m' ⁻¹ + (suc e/3 ⁻¹ + suc m' ⁻¹))) ∼⟨ {!!} ⟩
      suc n ⁻¹ + suc n ⁻¹ + (suc m' ⁻¹ + (suc e/3 ⁻¹ + suc m' ⁻¹)) ∼⟨ (≈->≤ {suc n ⁻¹ + suc n ⁻¹}{suc n ⁻¹ + suc n ⁻¹} refl) ℚ+-mono (ℚ≤lem₂ {e/3}{proj₁ (f {e/3})} ℚ+-mono (≈->≤ {suc e/3 ⁻¹}{suc e/3 ⁻¹} refl ℚ+-mono (ℚ≤lem₂ {e/3}{proj₁ (f {e/3})}))) ⟩
      suc n ⁻¹ + suc n ⁻¹ + e ∎
      where
        open IsEquivalence ℚ.isEquivalence using ()
          renaming (sym to ℚsym; trans to ℚtrans)
        open DecTotalOrder ℚ.decTotalOrder using () 
          renaming (reflexive to ≈->≤; trans to ≤trans; isPreorder to ℚisPreorder)
        open Pre record {isPreorder = ℚisPreorder}
        
    

{--}
{-λ {n} -> begin
  ∣ ℝ.f x n - ℝ.f y n ∣ ∼⟨ triang (ℝ.f x n) (ℝ.f x j) (ℝ.f y n) ⟩
  ∣ ℝ.f x n - ℝ.f x j ∣ + ∣ ℝ.f x j - ℝ.f y n ∣ ∼⟨  ≈->≤ {∣ ℝ.f x n - ℝ.f x j ∣}{∣ ℝ.f x n - ℝ.f x j ∣} refl ℚ+-mono  triang (ℝ.f x j) (ℝ.f y j) (ℝ.f y n)   ⟩
  ∣ ℝ.f x n - ℝ.f x j ∣ + (∣ ℝ.f x j - ℝ.f y j ∣ + ∣ ℝ.f y j - ℝ.f y n ∣) ∼⟨ ℝ.reg x {n}{j} ℚ+-mono (f ℚ+-mono ℝ.reg y {j}{n}) ⟩
  suc n ⁻¹ + suc j ⁻¹ + (suc j ⁻¹ + (suc j ⁻¹ + suc n ⁻¹)) ∼⟨ ? ⟩
  suc n ⁻¹ + 0' + (0' + (0' + suc n ⁻¹)) ∼⟨ {!!} ⟩
  suc n ⁻¹ + suc n ⁻¹ ∎-}

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
       
