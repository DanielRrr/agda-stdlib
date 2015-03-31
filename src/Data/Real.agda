module Data.Real where

open import Data.Rational as ℚ using (ℚ; -_ ; _*_; _÷_; _≤_; *≤*; ≃⇒≡; _-_; _+_; qcon; ∣_∣)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; _◃_; -_; +≤+; _⊖_) renaming (_+_ to _ℤ+_; _*_ to  _ℤ*_;_≤_ to ℤ_≤_)
open import Data.Nat as ℕ using (ℕ; suc; zero; compare; z≤n) renaming (_≤_ to ℕ_≤_)
open import Relation.Nullary.Decidable using (True; False; toWitness; fromWitness)
open import Data.Nat.Coprimality using (1-coprimeTo; sym; 0-coprimeTo-1)
open import Relation.Binary.Core using (_≡_; refl; Sym; _Respects_; Rel)
open import Relation.Binary.PropositionalEquality.Core using (trans; subst)
import Level

--Constructs a real number given a sequence approximating it and a proof that it is regular
record ℝ : Set where
  constructor _,_
  field
    f : ℕ -> ℚ
    reg : {n m : ℕ} -> (∣ (f n) ℚ.- (f m) ∣ ≤ (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))} ℚ.+ (+ 1 ÷ (suc m))  {fromWitness (λ {i} → 1-coprimeTo (suc m))})

---------------------------------------------------------------------------
--Equality

--Equality of real numbers.

infix 4 _≃_

_≃_ : Rel ℝ Level.zero
x ≃ y =  {n : ℕ} -> (∣ ℝ.f x n - ℝ.f y n ∣ ≤  (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))} ℚ.+ (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))})

--Proof that this is an equivalence relation-------------------

--Reflexity
refl-lem : {x : ℝ} ->  ({n : ℕ} -> (∣ ℝ.f x n - ℝ.f x n ∣ ≤ (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))} ℚ.+ (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))}))
refl-lem {x} = ℝ.reg x

reflex : (x : ℝ) -> x ≃ x
reflex x = refl-lem {x}

--For symmetry, the idea is to show that |x - y| = |y - x|
nomlemma : (x : ℚ) -> (ℚ.numerator x ≡ ℤ.- ℚ.numerator (ℚ.- x))
nomlemma (qcon -[1+ n ] d c) = refl
nomlemma (qcon (+ 0) d c) = refl
nomlemma (qcon (+ suc n) d c) = refl

delemma : (x : ℚ) -> (ℚ.denominator-1 x ≡ ℚ.denominator-1 (ℚ.- x))
delemma (qcon -[1+ n ] d c) = refl
delemma (qcon (+ 0) d c) = refl
delemma (qcon (+ suc n) d c) = refl

{-
--lemNeed to show - (x - y) ≡ (y - x)
lemNeed (x : ℚ) -> (y : ℚ) -> (ℚ.- (x ℚ.- y) ≡ (y ℚ.- x))
lemNeed (qcon -[1+ n ] d c) (qcon -[1+ n' ] d' c') =  
lemNeed (qcon -[1+ n ] d c) (qcon (+ 0) d' c')


--lemAnd abs(x) ≡ abs (-x)
--Lemma showing that |x - y| = |y- x|
diflem : {x : ℚ} {y : ℚ} -> (∣ (x - y) ∣ ≡ ∣ (y - x) ∣)
diflem {x} {y} = trans lemAnd (cong ∣_∣ lemNeed)
-}






-- -- --Examples

-- -- --Constructs a sequence of rationals approaching pi/4
-- -- LeibnizPi : ℕ -> ℚ
-- -- LeibnizPi zero = + 1 ÷ 1
-- -- LeibnizPi (suc n) = LeibnizPi n + (-[1+ 0 ] ^ (suc n) // suc ((suc n) ℕ.* 2))


-- -- -- --Proof that Leib-pi is regular
-- -- -- regLeibnizPi : (n m : ℕ) -> ∣ (LeibnizPi n) - (LeibnizPi m) ∣ ≤ (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))}  + (+ 1 ÷ (suc m))  {fromWitness (λ {i} → 1-coprimeTo (suc m))}
-- -- -- regLeibnizPi n m with compare n m
-- -- -- regLeibnizPi n m | equal n = ?
-- -- -- regLeibnizPi n m | greater n m = ?
-- -- -- regLeibnizPi n m | less n m = ?

-- -- ---OTHER APPROACH

-- -- --Lemma proving that a natural number minus itself is zero
-- -- n-lem : (n : ℕ) -> (n ℤ.⊖ n ≡ + zero)
-- -- n-lem zero = refl
-- -- n-lem (suc n) = n-lem n

-- --  --Lemma proving that an integer 
-- -- z-lem : (i : ℤ) -> (i ℤ.+ ℤ.- i ≡ + zero)
-- -- z-lem (+ ℕ.suc n) = n-lem (suc n)
-- -- z-lem (+ zero) = refl
-- -- z-lem -[1+ n ] = n-lem (suc n)

-- -- -- negative zero is positive zero
-- -- zerolemma : (+ zero ÷ 1) ≡ ℚ.- (+ zero ÷ 1)
-- -- zerolemma = refl



-- -- --The denominator of - +zero / d is d


-- -- subst : (A : Set) -> (B : A -> Set) -> (x y : A) -> (x ≡ y) -> (B x -> B y)
-- -- subst A B x .x refl p = p

-- -- equisym : {A : Set} {x y : A} -> (x ≡ y) -> (y ≡ x)
-- -- equisym refl = refl



-- -- --The denominator of x and -x are the same

-- --The nominator of -(p/q) is -p
-- nomlemma : (x : ℚ) -> (ℚ.numerator (ℚ.- x) ≡ ℤ.- ℚ.numerator (x))
-- nomlemma x with ℚ.numerator x | ℚ.denominator-1 x | toWitness (ℚ.isCoprime x)
-- ... | -[1+ n ] | d | c = refl
-- ... | + 0       | d | c = subst  0 d (sinj (equisym (0-coprimeTo-1 c))) refl
-- ... | + ℕ.suc n | d | c = refl




-- -- -- --Proof of additive inverse of rational numbers
-- -- -- --addinv : (x : ℚ) -> (x - x ≡ (+ zero ÷ 1))
-- -- -- --addinv x with ℚ.numerator x | ℚ.denominator-1 x | toWitness (ℚ.isCoprime x)
-- -- -- --...| n | d | c = {!!}



-- ---------ALTERNATE RATIONAL CONSTRUCTOR-----------------------

-- -- --Creates a rational number in reduced form (no co-prime proof is needed)
-- -- infixl 6 _//_
-- -- _//_ : ℤ -> (denominator : ℕ) -> {≢0 : False (ℕ._≟_ denominator 0)} -> ℚ
-- -- (z // zero) {≢0 = ()}
-- -- z // suc n = (z ÷ 1) {fromWitness (λ {i} → sym(1-coprimeTo (ℤ.∣ z ∣)))} * ( + 1  ÷ suc n) {fromWitness (λ {i} → 1-coprimeTo (suc n))}

-- -- --Easier version of addition of rationals, using  _//_ to create the result.
-- -- _+_ : ℚ -> ℚ -> ℚ
-- -- p₁ + p₂ =
-- --   let n₁ = ℚ.numerator p₁
-- --       d₁ = ℕ.suc (ℚ.denominator-1 p₁)
-- --       n₂ = ℚ.numerator p₂
-- --       d₂ = ℕ.suc (ℚ.denominator-1 p₂)
-- --       n = (n₁ ℤ.* + d₂) ℤ.+ (n₂ ℤ.* + d₁)
-- --       d = d₁ ℕ.* d₂
-- --   in n // d

-- -- --Subtraction of rationals 

-- -- _-_ : ℚ -> ℚ -> ℚ
-- -- p₁ - p₂ = p₁ + (ℚ.- p₂)
