module Data.Real where

open import Data.Rational as ℚ using (ℚ; -_ ; _*_; _÷_; _≤_; *≤*; ≃⇒≡; _-_; _+_; qcon; ∣_∣; _≤?_; NonZero; normalize; gcd≢0)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; _◃_; -_; +≤+; _⊖_; sign) renaming (_+_ to _ℤ+_; _*_ to  _ℤ*_;_≤_ to ℤ_≤_)
open import Data.Sign using (Sign)
open import Data.Nat as ℕ using (ℕ; suc; zero; compare; z≤n) renaming (_≤_ to ℕ_≤_)
open import Relation.Nullary.Decidable using (True; False; toWitness; fromWitness)
open import Data.Nat.Coprimality using (1-coprimeTo; sym; 0-coprimeTo-1)
open import Relation.Binary.Core using (_≡_; refl; Sym; Rel; Reflexive; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality.Core using (trans; subst)
import Level
open import Algebra.Properties.Ring using (-‿*-distribˡ)
open import Algebra using (CommutativeRing; Ring)
open import Data.Integer.Properties using (commutativeRing; abs-◃ )
import Data.Nat.Coprimality as C using (sym; Coprime; coprime?; Bézout-coprime; 0-coprimeTo-1; 1-coprimeTo; coprime-gcd)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; subst; cong; cong₂)
open import Relation.Binary.Core as BC using (Transitive)
open import Data.Nat.GCD
open import Data.Nat.Divisibility as ℕDiv using (_∣_; divides; quotient)
open import Data.Product

--Constructs a real number given a sequence approximating it and a proof that it is regular
record ℝ : Set where
  constructor Real
  field
    f : ℕ -> ℚ
    reg : {n m : ℕ} -> (∣ (f n) ℚ.- (f m) ∣ ≤ (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))} ℚ.+ (+ 1 ÷ (suc m))  {fromWitness (λ {i} → 1-coprimeTo (suc m))})

  ---------------------------------------EQUALITY-------------------------
--Equality

--Equality of real numbers.

infix 4 _≃_

_≃_ : Rel ℝ Level.zero
x ≃ y =  {n : ℕ} -> (∣ ℝ.f x n - ℝ.f y n ∣ ≤  (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))} ℚ.+ (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))})

--Proof that this is an equivalence relation-------------------

--Reflexity
refl-lem : {x : ℝ} ->  ({n : ℕ} -> (∣ ℝ.f x n - ℝ.f x n ∣ ≤ (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))} ℚ.+ (+ 1 ÷ (suc n))  {fromWitness (λ {i} → 1-coprimeTo (suc n))}))
refl-lem {x} = ℝ.reg x



{-----------------__TRANSITIVITY---------------------------
  ttrans : {x y z : ℝ} -> (x ≃ y) -> (y ≃ z) -> (x ≃ z))
  ttrans = trans
    where
    open ℚ.DecTotalOrder
-} 

--For symmetry, the idea is to show that |x - y| = |y - x|
nomlemma : (x : ℚ) -> (ℚ.numerator (ℚ.- x) ≡ ℤ.- ℚ.numerator x)
nomlemma (qcon -[1+ n ] d c) = refl
nomlemma (qcon (+ 0) d c) = refl
nomlemma (qcon (+ suc n) d c) = refl

delemma : (x : ℚ) -> (ℚ.denominator-1 (ℚ.- x) ≡ ℚ.denominator-1 x)
delemma (qcon -[1+ n ] d c) = refl
delemma (qcon (+ 0) d c) = refl
delemma (qcon (+ suc n) d c) = refl

wheretofindthislemma? : (z : ℤ) -> (ℤ.∣ z ∣ ≡ ℤ.∣ ℤ.- z ∣)
wheretofindthislemma? (+ zero) = refl
wheretofindthislemma? (+ suc n) = refl
wheretofindthislemma? -[1+ z ] = refl

--Funkar också
colemma : {x : ℚ} -> ((C.Coprime (ℤ.∣ ℚ.numerator x ∣) (suc (ℚ.denominator-1 x))) ≡ (C.Coprime (ℤ.∣ ℤ.- ℚ.numerator x ∣)(suc (ℚ.denominator-1 x))))
colemma {x} = cong (λ a -> (C.Coprime a (suc (ℚ.denominator-1 x)))) (wheretofindthislemma? (ℚ.numerator x))

--Funkar!
clemma : {x : ℚ} -> (True (C.coprime? ℤ.∣ ℚ.numerator x ∣ (suc (ℚ.denominator-1 x)))  ≡ True (C.coprime? ℤ.∣ ℤ.- (ℚ.numerator x) ∣ (suc (ℚ.denominator-1 x))))
clemma {x} = cong (λ a -> (True (C.coprime? a (suc (ℚ.denominator-1 x))))) (wheretofindthislemma? (ℚ.numerator x))

{-
--Lemma showing ℚ.- (qcon n d c) ≡ (qcon (ℤ.- n) d c)
minQlemma : (x : ℚ) -> ((ℚ.- x) ≡ (qcon (ℤ.- ℚ.numerator x) (ℚ.denominator-1 x) ((fromWitness (λ {i} -> (subst (λ n -> (C.Coprime n (suc (ℚ.denominator-1 x)))) (wheretofindthislemma? (ℚ.numerator x)) (toWitness (ℚ.isCoprime x))) )))))
minQlemma (qcon (+ zero) d c)  = cong (λ a -> (qcon (ℤ.- (+ zero)) (d) a)) {!colemma {qcon (+ zero) d c}!} --(colemma {(qcon (+ zero) d c)})
minQlemma (qcon (+ ℕ.suc n) d c) = {!!} --refl
minQlemma (qcon -[1+ n ] d c) = {!!} --refl
-}
{-
minQlemma : (x : ℚ) -> ((ℚ.- x) ≡ ((ℤ.- ℚ.numerator x) ÷ suc (ℚ.denominator-1 x)) )
minQlemma (qcon -[1+ n ] d c) = refl
minQlemma (qcon (+ 0) d c) = refl
minQlemma (qcon (+ ℕ.suc n) d c) = refl
-}
{-
minQlemma (qcon n d c) = trans (cong (λ b -> (((b) ÷ suc (d)) {fromWitness (λ {i} -> (colemma (toWitness c)))})) (nomlemma (qcon n d c))) 
  (cong (λ b -> ((ℤ.- n) ÷ suc (b)) {?}) (delemma (qcon n d c)))
-}

ZRing : Ring _ _
ZRing = record
  { Carrier           = ℤ
  ; _≈_               = _≡_
  ; _+_               = ℤ._+_
  ; _*_               = ℤ._*_
  ; -_                = ℤ.-_
  ; 0#                = + 0
  ; 1#                = + 1
  ; isRing = CommutativeRing.isRing commutativeRing
   }

mulemma : (z₁ z₂ : ℤ) -> ((ℤ.- z₁) ℤ.*  z₂ ≡ ℤ.- (z₁ ℤ.* z₂))
mulemma x y = -‿*-distribˡ (ZRing) x y


{-
mulemma (+ zero) z = refl
mulemma (+ suc n) -[1+ n₂ ] = refl
mulemma (+ suc n) (+ suc n₂) = refl
mulemma (+ suc n) (+ zero) = refl
mulemma -[1+ n ] z = refl


mulemma (+ n₁) -[1+ n₂ ] = {!!}
mulemma -[1+ n ] (+ n₂) = {!!} 
mulemma -[1+ n ] -[1+ n₂ ] = {!!} 

ℤ.sign (ℤ.- (+ n₁)) .Data.Sign.S* .Data.Sign.Sign.+ ◃
ℤ.∣ ℤ.- (+ n₁) ∣ ℕ.* n₂
-}

--ℤ.- (.Data.Sign.Sign.+ ◃ n₁ ℕ.* n₂)
{-
Lem : (x y : ℚ) -> (x - y ≡ 
     ℚ.reduce (ℚ.numerator x ℤ.* + suc (ℚ.denominator-1 (ℚ.- y)) ℤ.- 
     ℚ.numerator y ℤ.* + suc (ℚ.denominator-1 x))
     (suc (ℚ.denominator-1 x) ℕ.* suc (ℚ.denominator-1 (ℚ.- y))))
Lem (qcon n₁ d₁ c₁) (qcon n₂ d₂ c₂) = subst ? (delemma y) refl
-}

---------------------------------???----------------------------
{-
--stupidattempt
stupidlem : (z : ℤ) -> (n : ℕ) -> {n≢0 : ℚ.NonZero n} -> (ℚ.- (ℚ.reduce z n {n≢0}) ≡ ℚ.reduce (ℤ.- z) n)
stupidlem z 0 {()}
stupidlem z d {d≢0} with stupidway ℤ.∣ z ∣ d {d≢0}
stupidlem z d {d≢0} | (nn , nd , nd≢0 , nc) = refl --{!!}
-}

--NTS:
reducelem : (z : ℤ) -> (n : ℕ) -> {n≢0 : ℚ.NonZero n} -> (ℚ.- (ℚ.reduce z n {n≢0}) ≡ ℚ.reduce (ℤ.- z) n)
reducelem (+ 0) n = refl
reducelem z 0 {()}
reducelem z (suc n) {n≢0} with (gcd≢0 ℤ.∣ z ∣ (suc n))
reducelem z (suc n){n≢0} | g , G , g≢0 with normalize {ℤ.∣ z ∣} {suc n} {g} {n≢0}{g≢0} G
reducelem -[1+ n ] (suc n₁) | g , G , g≢0 | nn , nd , nd≢0 , nc = ?
reducelem (+ n) (suc n₁) | g , G , g≢0 | nn , nd , nd≢0 , nc = {!!}

{-
reducelem z n {n≢0}| (suc g , GCD.is (_ , g|n) _) = ?
reducelem z n {n≢0}| (0 , GCD.is (_ , 0|n) _) with ℕDiv.0∣⇒≡0 0|n
reducelem z .0 {()} | (0 , GCD.is (_ , 0|n) _) | refl with normalize {ℤ.∣ z ∣} {suc n₂} {ℕ.suc g} G
reducelem z (suc n₂) {n≢0} | (suc g , G) | (nn , nd , nd≢0 , nc) = ? --refl --(ℤ.abs-◃ (sign n) nn)
-}
{-
testfest : {x y : ℚ} -> (ℚ.- (x ℚ.- y) ≡ y ℚ.- x)
testfest {qcon -[1+ n₁ ] d₁ c₁} {qcon -[1+ n₂ ] d₂ c₂} = {!refl!}
testfest {qcon -[1+ n₁ ] d₁ c₁} {qcon (+ n₂) d₂ c₂} = {!!}
testfest {qcon (+ n₁) d₁ c₁} {qcon -[1+ n₂ ] d₂ c₂} = {!!}
testfest {qcon (+ n₁) d₁ c₁} {qcon (+ n₂) d₂ c₂} = {!refl!}
-}

{-
--This lemma gives us a handy way of expressing x - y
Lemm : (x y : ℚ) -> (x - y ≡ 
     ℚ.reduce (ℚ.numerator x ℤ.* + suc (ℚ.denominator-1 y) ℤ.- 
     ℚ.numerator y ℤ.* + suc (ℚ.denominator-1 x))
     (suc (ℚ.denominator-1 x) ℕ.* suc (ℚ.denominator-1 y)))
Lemm x y = trans (cong (λ a -> (ℚ.reduce 
     (ℚ.numerator x ℤ.* + suc a ℤ.+ 
     ℚ.numerator (ℚ.- y) ℤ.* + suc (ℚ.denominator-1 x))
     (suc (ℚ.denominator-1 x) ℕ.* suc a))) (delemma y)) 
     (trans (cong (λ a -> (ℚ.reduce (ℚ.numerator x ℤ.* + suc (ℚ.denominator-1 y) ℤ.+ 
     a ℤ.* + suc (ℚ.denominator-1 x))
     (suc (ℚ.denominator-1 x) ℕ.* suc (ℚ.denominator-1 y)))) (nomlemma y)) 
     ((cong (λ ab -> (ℚ.reduce (ℚ.numerator x ℤ.* + suc (ℚ.denominator-1 y) ℤ.+ 
     ab)
     (suc (ℚ.denominator-1 x) ℕ.* suc (ℚ.denominator-1 y)))))  (mulemma (ℚ.numerator y)(+ suc (ℚ.denominator-1 x)))))
-}
{-trans (cong (λ a -> (ℚ.reduce 
     (ℚ.numerator x ℤ.* + suc a ℤ.+ 
     ℚ.numerator (ℚ.- y) ℤ.* + suc (ℚ.denominator-1 x))
     (suc (ℚ.denominator-1 x) ℕ.* suc a))) (delemma y)) (trans ( trans (cong (λ a -> (ℚ.reduce (ℚ.numerator x ℤ.* + suc (ℚ.denominator-1 y) ℤ.+ 
     a ℤ.* + suc (ℚ.denominator-1 x))
     (suc (ℚ.denominator-1 x) ℕ.* suc (ℚ.denominator-1 y)))) (nomlemma y)) ({!!}) ))
-}

{-subst  (λ a -> (x - y ≡
  ℚ.reduce
  (ℚ.ℚ.numerator x ℤ* + suc a ℤ.-
  ℚ.ℚ.numerator y ℤ* + suc (ℚ.ℚ.denominator-1 x))
  (suc (ℚ.ℚ.denominator-1 x) ℕ.* suc (ℚ.ℚ.denominator-1 y)))) (delemma y) (refl
-}

{-----------------------           x - y evaluates to
ℚ.reduce
(ℚ.ℚ.numerator x ℤ.* (+ suc (ℚ.ℚ.denominator-1 (ℚ.- y)))
 ℤ+
 ℚ.ℚ.numerator (ℚ.- y) ℤ.* suc (ℚ.ℚ.denominator-1 x))
 (suc
 (ℚ.ℚ.denominator-1 (ℚ.- y) ℕ.+
  ℚ.ℚ.denominator-1 x ℕ.* suc (ℚ.ℚ.denominator-1 (ℚ.- y))))
-}
{-
absredlem : (z : ℤ)(n : ℕ) -> (ℚ.∣ (ℚ.reduce z n) ∣ ≡ ℚ.reduce (+ ℤ.∣ z ∣) n)
absredlem z n = refl

reducelem : (z : ℤ)(n : ℕ) -> (ℚ.- (ℚ.reduce z n) ≡ ℚ.reduce (ℤ.- z) n)
reducelem -[1+ n₁ ] n₂ = {!refl!}
reducelem (+ zero) n₂ = {!!}
reducelem (+ suc n₁) n₂ = {!!}

---Problemet är att det är högerledet vi vill ändra på!

lemNeed : (x : ℚ) -> (y : ℚ) -> (ℚ.- (x ℚ.- y) ≡ ℚ.reduce ((ℚ.numerator y) ℤ.* + suc (ℚ.denominator-1 x) ℤ.- 
     ℚ.numerator x ℤ.* + suc (ℚ.denominator-1 y))
     (suc (ℚ.denominator-1 y) ℕ.* suc (ℚ.denominator-1 x)))
lemNeed (qcon -[1+ n₁ ] d₁ c₁) (qcon -[1+ n₂ ] d₂ c₂) = {!!} --cong (λ a -> (ℚ.- a)) (Lemm (qcon -[1+ n₁ ] d₁ c₁) (qcon -[1+ n₂ ] d₂ c₂))
lemNeed (qcon -[1+ n₁ ] d₁ c₁) (qcon (+ zero) d₂ c₂) = {!!}
lemNeed (qcon -[1+ n₁ ] d₁ c₁) (qcon (+ (suc n₂)) d₂ c₂) = {!!}
lemNeed (qcon (+ zero) d₁ c₁) (qcon -[1+ n₂ ] d₂ c₂) = {!!}
lemNeed (qcon (+ suc n₁) d₁ c₁) (qcon -[1+ n₂ ] d₂ c₂) = {!!}
lemNeed (qcon (+ zero) d₁ c₁) (qcon (+ zero) d₂ c₂) = {!!}
lemNeed (qcon (+ zero) d₁ c₁) (qcon (+ suc n₂) d₂ c₂) = {!!}
lemNeed (qcon (+ suc n₁) d₁ c₁) (qcon (+ zero) d₂ c₂) = {!!}
lemNeed (qcon (+ suc n₁) d₁ c₁) (qcon (+ suc n₂) d₂ c₂) = {!!}
-}
--lemNeed (qcon (+ suc n₁) d₁ c₁) (qcon (+ suc n₂) d₂ c₂) = trans (cong (λ a -> (ℚ.- a)) (Lemm (qcon (+ suc n₁) d₁ c₁) (qcon (+ suc n₂) d₂ c₂))) {!cong (λ a -> ℚ.reduce a ((suc (ℚ.denominator-1 y)) ℤ.* (suc (ℚ.denominator-1 x)))) (nomlemma )!}

-- -- subst : (A : Set) -> (B : A -> Set) -> (x y : A) -> (x ≡ y) -> (B x -> B y)
-- -- subst A B x .x refl p = p
{-
Lemm (qcon (+ n₁) d₁ c₁) (qcon (+ n₂) d₂ c₂) = {!subst Lemm (delemma x) d₂!}
Lemm (qcon (+ n₁) d₁ c₁) (qcon -[1+ n₂ ] d₂ c₂) = {!!}
Lemm (qcon -[1+ n₁ ] d₁ c₁) (qcon (+ n₂) d₂ c₂) = {!!}
Lemm (qcon -[1+ n₁ ] d₁ c₁) (qcon -[1+ n₂ ] d₂ c₂) = {!!}

-------------------____TRANS_________-----------------------------





--------------------------------

?0 : ℚ.-
ℚ.reduce
((ℤ.sign (+ n₁) .Data.Sign.S* .Data.Sign.Sign.+ ◃
  ℤ.∣ + n₁ ∣ ℕ.* suc (ℚ.ℚ.denominator-1 (ℚ.- qcon (+ suc n₂) d₂ c₂)))
 ℤ+
 (ℤ.sign (ℚ.ℚ.numerator (ℚ.- qcon (+ suc n₂) d₂ c₂)) .Data.Sign.S*
  .Data.Sign.Sign.+
  ◃ ℤ.∣ ℚ.ℚ.numerator (ℚ.- qcon (+ suc n₂) d₂ c₂) ∣ ℕ.* suc d₁))
(suc
 (ℚ.ℚ.denominator-1 (ℚ.- qcon (+ suc n₂) d₂ c₂) ℕ.+
  d₁ ℕ.* suc (ℚ.ℚ.denominator-1 (ℚ.- qcon (+ suc n₂) d₂ c₂))))
≡ qcon (+ n) d c


--lemNeed to show - (x - y) ≡ (y - x)
lemNeed : (x : ℚ) -> (y : ℚ) -> (ℚ.- (x ℚ.- y) ≡ y ℚ.- x)
lemNeed x y with x - y
... | (qcon (+ n) d c) = {!!}
-}
{-
lemNeed (qcon (+ n₁) d₁ c₁) (qcon (+ n₂) d₂ c₂) | (qcon (+ n) d c) = {!!}
lemNeed (qcon (+ n₁) d₁ c₁) (qcon (+ zero) d₂ c₂) | (qcon (+ n) d c) = {!!}
lemNeed (qcon (+ n₁) d₁ c₁) (qcon -[1+ n₂ ] d₂ c₂) | (qcon (+ n) d c) = {!!}
lemNeed (qcon -[1+ n₁ ] d₁ c₁) (qcon (+ n₂) d₂ c₂) | (qcon (+ n) d c) = {!!}
lemNeed (qcon -[1+ n₁ ] d₁ c₁) (qcon -[1+ n₂ ] d₂ c₂) | (qcon (+ n) d c) = {!!}


... | (qcon -[1+ n ] d c) = {!!}

-}
--Maybe we can go straight to |x + y| = ||

{-

--lemAnd abs(x) ≡ abs (-x)
--Lemma showing that |x - y| = |y- x|
diflem : {x : ℚ} {y : ℚ} -> (∣ (x - y) ∣ ≡ ∣ (y - x) ∣)
diflem {x} {y} = trans lemAnd (cong ∣_∣ lemNeed)
-}

--Transitivity

--≡--


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
