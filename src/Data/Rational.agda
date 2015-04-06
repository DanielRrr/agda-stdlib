------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

module Data.Rational where

import Algebra
import Data.Sign as S
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
import Data.Bool.Properties as Bool
open import Function
open import Data.Product
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; _◃_; sign)
open import Data.Integer.Divisibility as ℤDiv using (Coprime)
import Data.Integer.Properties as ℤ
open import Data.Nat.GCD
open import Data.Nat.Divisibility as ℕDiv using (_∣_; divides; quotient)
import Data.Nat.Coprimality as C using (sym; Coprime; coprime?; Bézout-coprime; 0-coprimeTo-1; 1-coprimeTo; coprime-gcd)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Sum
open import Data.String using (String; _++_)
import Level
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; subst; cong; cong₂)
open P.≡-Reasoning

infix  8 -_ 1/_
--infixl 7  _/_ _*_
--infixl 6 _-_ _+_

------------------------------------------------------------------------
-- The definition

-- Rational numbers in reduced form. Note that there is exactly one
-- representative for every rational number. (This is the reason for
-- using "True" below. If Agda had proof irrelevance, then it would
-- suffice to use "isCoprime : Coprime numerator denominator".)

record ℚ : Set where
  constructor qcon
  field
    numerator     : ℤ
    denominator-1 : ℕ
    isCoprime     : True (C.coprime? ℤ.∣ numerator ∣ (suc denominator-1))

  denominator : ℤ
  denominator = + suc denominator-1

  coprime : Coprime numerator denominator
  coprime = toWitness isCoprime

-- Constructs rational numbers. The arguments have to be in reduced
-- form.

infixl 7 _÷_

_÷_ : (numerator : ℤ) (denominator : ℕ)
      {coprime : True (C.coprime? ℤ.∣ numerator ∣ denominator)}
      {≢0 : False (ℕ._≟_ denominator 0)} →
      ℚ
(n ÷ zero) {≢0 = ()}
(n ÷ suc d) {c} =
  record { numerator = n; denominator-1 = d; isCoprime = c }

private

  -- Note that the implicit arguments do not need to be given for
  -- concrete inputs:

  0/1 : ℚ
  0/1 = + 0 ÷ 1

  -½ : ℚ
  -½ = (ℤ.- + 1) ÷ 2

------------------------------------------------------------------------
-- Two useful lemmas to help with operations on rationals

NonZero : ℕ → Set
NonZero 0       = ⊥
NonZero (suc _) = ⊤

-- normalize takes two natural numbers, say 6 and 21 and their gcd 3, and
-- returns them normalized as 2 and 7 and a proof that they are coprime

normalize : ∀ {m n g} → {n≢0 : NonZero n} → {g≢0 : NonZero g} →
            GCD m n g → Σ[ p ∈ ℕ ] Σ[ q ∈ ℕ ] False (q ℕ.≟ 0) × C.Coprime p q
normalize {m} {n} {0} {_} {()} _
normalize {m} {n} {ℕ.suc g} {_} {_} G with Bézout.identity G
normalize {m} {.0} {ℕ.suc g} {()} {_}
  (GCD.is (divides p m≡pg' , divides 0 refl) _) | _
normalize {m} {n} {ℕ.suc g} {_} {_}
  (GCD.is (divides p m≡pg' , divides (ℕ.suc q) n≡qg') _) | Bézout.+- x y eq =
    (p , ℕ.suc q , tt , C.Bézout-coprime {p} {ℕ.suc q} {g} (Bézout.+- x y
               (begin
                 ℕ.suc g ℕ.+ y ℕ.* (ℕ.suc q ℕ.* ℕ.suc g)
               ≡⟨ cong (λ h → ℕ.suc g ℕ.+ y ℕ.* h) (P.sym n≡qg') ⟩
                 ℕ.suc g ℕ.+ y ℕ.* n
               ≡⟨ eq ⟩
                 x ℕ.* m
               ≡⟨ cong (λ h → x ℕ.* h) m≡pg' ⟩
                 x ℕ.* (p ℕ.* ℕ.suc g) ∎)))
normalize {m} {n} {ℕ.suc g} {_} {_}
  (GCD.is (divides p m≡pg' , divides (ℕ.suc q) n≡qg') _) | Bézout.-+ x y eq =
    (p , ℕ.suc q , tt , C.Bézout-coprime {p} {ℕ.suc q} {g} (Bézout.-+ x y
               (begin
                 ℕ.suc g ℕ.+ x ℕ.* (p ℕ.* ℕ.suc g)
               ≡⟨ cong (λ h → ℕ.suc g ℕ.+ x ℕ.* h) (P.sym m≡pg') ⟩
                 ℕ.suc g ℕ.+ x ℕ.* m
               ≡⟨ eq ⟩
                 y ℕ.* n
               ≡⟨ cong (λ h → y ℕ.* h) n≡qg' ⟩
                 y ℕ.* (ℕ.suc q ℕ.* ℕ.suc g) ∎)))


-- a version of gcd that returns a proof that the result is non-zero given
-- that one of the inputs is non-zero
{-
gcd≢0 : (m n : ℕ) → {m≢0 : NonZero m} → ∃ λ d → GCD m n d × NonZero d
gcd≢0 m  n {m≢0} with gcd m n
gcd≢0 m  n {m≢0} | (0 , GCD.is (0|m , _) _) with ℕDiv.0∣⇒≡0 0|m
gcd≢0 .0 n {()}  | (0 , GCD.is (0|m , _) _) | refl
gcd≢0 m  n {_}   | (ℕ.suc d , G) = (ℕ.suc d , G , tt)
-}

gcd≢0 : (m n : ℕ) → {n≢0 : NonZero n} → ∃ λ d → GCD m n d × NonZero d
gcd≢0 m  n {m≢0} with gcd m n
gcd≢0 m  n {m≢0} | (0 , GCD.is (_ , 0|n) _) with ℕDiv.0∣⇒≡0 0|n
gcd≢0 m .0 {()}  | (0 , GCD.is (_ , 0|n) _) | refl
gcd≢0 m  n {_}   | (ℕ.suc d , G) = (ℕ.suc d , G , tt)

--Reduces a given quotient to its coprime form
reduce :  ℤ -> (d : ℕ) -> {d≢0 : NonZero d} -> ℚ
reduce (+ 0) d = (+ 0 ÷ 1)
reduce n 0 {()}
reduce n d {d≢0} =
  let
      (g , G , g≢0) = gcd≢0 ℤ.∣ n ∣ d {d≢0}
      (nn , nd , nd≢0 , nc) = normalize {ℤ.∣ n ∣} {d} {g} {d≢0} {g≢0} G
  in ((sign n ◃ nn) ÷ nd){fromWitness (λ {i} → subst (λ h → C.Coprime h nd) (P.sym (ℤ.abs-◃ (sign n) nn)) nc)}
     {nd≢0}

{-
--Combining these two gives us a useful way to reduce quotients to rational numbers. Takes denominator-1 as second argument
reduce :  ℤ -> ℕ -> ℚ
reduce (+ 0) d = (+ 0 ÷ 1)
reduce n 0  = (n ÷ 1) {fromWitness (λ {i} -> C.sym (C.1-coprimeTo ℤ.∣ n ∣))}
reduce (+ (suc n)) d =
  let
      (g , G , g≢0) = gcd≢0  ℤ.∣ + (suc n) ∣ (suc d) {tt}
      (nn , nd , nd≢0 , nc) = normalize {ℤ.∣ + (suc n) ∣} {suc d} {g} {_} {g≢0} G
  in ((sign (+ (suc n)) ◃ nn) ÷ nd){fromWitness (λ {i} → subst (λ h → C.Coprime h nd) (P.sym (ℤ.abs-◃ (sign (+ (suc n))) nn)) nc)}
     {nd≢0}
reduce -[1+ n ] d =
  let
      (g , G , g≢0) = gcd≢0  ℤ.∣ -[1+ n ] ∣ (suc d) {_}
      (nn , nd , nd≢0 , nc) = normalize {ℤ.∣ -[1+ n ] ∣} {suc d} {g} {_} {g≢0} G
  in ((sign (-[1+ n ]) ◃ nn) ÷ nd){fromWitness (λ {i} → subst (λ h → C.Coprime h nd) (P.sym (ℤ.abs-◃ (sign (-[1+ n ])) nn)) nc)}
     {nd≢0}
-}
------------------------------------------------------------------------------
-- Operations on rationals: unary -, reciprocal, multiplication, addition

-- unary negation
-- 
-- Andreas Abel says: Agda's type-checker is incomplete when it has to handle
-- types with leading hidden quantification, such as the ones of Coprime m n
-- and c.  A work around is to use hidden abstraction explicitly.  In your
-- case, giving λ {i} -> c works.  Not pretty, but unavoidable until we
-- improve on the current heuristics. I recorded this as a bug
-- http://code.google.com/p/agda/issues/detail?id=1079

-_ : ℚ → ℚ
- (qcon -[1+ n ] d c) = (+ ℕ.suc n ÷ ℕ.suc d) {c}
- (qcon (+ 0) d c) = (+ 0 ÷ suc d) {c}
- (qcon (+ ℕ.suc n) d c) = (-[1+ n ]  ÷ ℕ.suc d) {c}

-- reciprocal: requires a proof that the numerator is not zero

1/_ : (p : ℚ) → {n≢0 : NonZero ℤ.∣ ℚ.numerator p ∣} → ℚ
1/_ (qcon (+ suc n₁) d₁ c₁) = ((+ suc d₁) ÷ (suc n₁)) {fromWitness (λ {i} → C.sym (toWitness c₁))}
1/_ (qcon (+ zero) d₂ c₂) {()}
1/_ (qcon -[1+ n₃ ] d₃ c₃) {n≢0} = (-[1+ d₃ ] ÷ (suc n₃)) {fromWitness (λ {i} → C.sym (toWitness c₃))}

{-
-- multiplication

private 

   helper* : (n₁ : ℤ) → (d₁ : ℕ) → (n₂ : ℤ) → (d₂ : ℕ) →
             {n≢0 : NonZero ℤ.∣ n₁ ℤ.* n₂ ∣} →
             {d≢0 : NonZero (d₁ ℕ.* d₂)} →
             ℚ
   helper* n₁ d₁ n₂ d₂ {n≢0} {d≢0} =
     let n = n₁ ℤ.* n₂
         d = d₁ ℕ.* d₂
         (g , G , g≢0) = gcd≢0  ℤ.∣ n ∣ d {n≢0}
         (nn , nd , nd≢0 , nc) = normalize {ℤ.∣ n ∣} {d} {g} {d≢0} {g≢0} G
     in ((sign n ◃ nn) ÷ nd) 
        {fromWitness (λ {i} → 
           subst (λ h → C.Coprime h nd) (P.sym (ℤ.abs-◃ (sign n) nn)) nc)}
        {nd≢0}

_*_ : ℚ → ℚ → ℚ
(qcon (+ 0) d c) * p = + 0 ÷ 1
p * (qcon (+ 0) d c) = + 0 ÷ 1
(qcon (+ suc n₁) d₁ c₁) * (qcon (+ suc n₂) d₂ c₂) = helper* (+ suc n₁)(suc d₁)(+ suc n₂)(suc d₂)
(qcon (+ suc n₁) d₁ c₁) * (qcon -[1+ n₂ ] d₂ c₂) = helper* (+ suc n₁)(suc d₁) -[1+ n₂ ](suc d₂)
(qcon -[1+ n₁ ] d₁ c₁) * (qcon (+ suc n₂) d₂ c₂) = helper* -[1+ n₁ ](suc d₁)(+ suc n₂)(suc d₂)
(qcon -[1+ n₁ ] d₁ c₁) * (qcon -[1+ n₂ ] d₂ c₂) = helper* -[1+ n₁ ](suc d₁)-[1+ n₂ ](suc d₂)
-}

_*_ : ℚ -> ℚ -> ℚ
(qcon n₁ d₁ c₁) * (qcon n₂ d₂ c₂) = reduce (n₁ ℤ.* n₂)((suc d₁) ℕ.* (suc d₂))


--En god ide skulle kunna vara att skriva om helper* så att det är en funktion som bara normaliserar två element, n₁*n₂ och d₁*d₂. Man skulle kanske kunna skriva en enklare version av normalize och bara använda sig av den hela tiden i alla de här funktionerna
{-
--my take on addition
_+_ : ℚ → ℚ → ℚ
(qcon (+ 0) d₁ c₁) + p₂ = p₂
p₁ + (qcon (+ 0) d₂ c₂) = p₁
(qcon (+ suc n₁) d₁ c₁) + (qcon (+ suc n₂) d₂ c₂) = helper* (
-}
{-
-- addition

private 

  helper+ : (n : ℤ) → (d : ℕ) → {d≢0 : NonZero d} → ℚ
  helper+ (+ 0) d {d≢0} = + 0 ÷ 1
  helper+ (+ ℕ.suc n) d {d≢0} =
    let (g , G , g≢0) = gcd≢0 ℤ.∣ + ℕ.suc n ∣ d {tt}
        (nn , nd , nd≢0 , nc) = normalize {ℤ.∣ + ℕ.suc n ∣} {d} {g} {d≢0} {g≢0} G
    in ((S.+ ◃ nn) ÷ nd) 
       {fromWitness (λ {i} → 
          subst (λ h → C.Coprime h nd) (P.sym (ℤ.abs-◃ S.+ nn)) nc)}
       {nd≢0}
  helper+ -[1+ n ] d {d≢0} =
    let (g , G , g≢0) = gcd≢0 ℤ.∣ -[1+ n ] ∣ d {tt}
        (nn , nd , nd≢0 , nc) = normalize {ℤ.∣ -[1+ n ] ∣} {d} {g} {d≢0} {g≢0} G
    in ((S.- ◃ nn) ÷ nd) 
       {fromWitness (λ {i} → 
          subst (λ h → C.Coprime h nd) (P.sym (ℤ.abs-◃ S.- nn)) nc)}
       {nd≢0}

_+_ : ℚ → ℚ → ℚ
p₁ + p₂ =
  let n₁ = ℚ.numerator p₁
      d₁ = ℕ.suc (ℚ.denominator-1 p₁)
      n₂ = ℚ.numerator p₂
      d₂ = ℕ.suc (ℚ.denominator-1 p₂)
      n = (n₁ ℤ.* + d₂) ℤ.+ (n₂ ℤ.* + d₁)
      d = d₁ ℕ.* d₂
  in helper+ n d
-}

_+_ : ℚ → ℚ → ℚ
(qcon n₁ d₁ c₁) + (qcon n₂ d₂ c₂) = reduce ((n₁ ℤ.* + (suc d₂)) ℤ.+ (n₂ ℤ.* + (suc  d₁)))((suc d₁) ℕ.* (suc d₂))


-- subtraction and division

_-_ : ℚ → ℚ → ℚ
p₁ - p₂ = p₁ + (- p₂)

_/_ : (p₁ p₂ : ℚ) → {n≢0 : NonZero ℤ.∣ ℚ.numerator p₂ ∣} → ℚ
_/_ p₁ p₂ {n≢0} = p₁ * (1/_ p₂ {n≢0})


--absolute value of a rational number
∣_∣ : ℚ -> ℚ
∣ p ∣ = (+ ℤ.∣ ℚ.numerator p ∣ ÷ ( suc (ℚ.denominator-1 p))) {ℚ.isCoprime p}

-- conventional printed representation

show : ℚ → String
show p = ℤ.show (ℚ.numerator p) ++ "/" ++ ℕshow (ℕ.suc (ℚ.denominator-1 p))

------------------------------------------------------------------------
-- Equality

-- Equality of rational numbers.

infix 4 _≃_

_≃_ : Rel ℚ Level.zero
p ≃ q = numerator p ℤ.* denominator q ≡
        numerator q ℤ.* denominator p
  where open ℚ

-- _≃_ coincides with propositional equality.

≡⇒≃ : _≡_ ⇒ _≃_
≡⇒≃ refl = refl

≃⇒≡ : _≃_ ⇒ _≡_
≃⇒≡ {i = p} {j = q} =
  helper (numerator p) (denominator-1 p) (isCoprime p)
         (numerator q) (denominator-1 q) (isCoprime q)
  where
  open ℚ

  helper : ∀ n₁ d₁ c₁ n₂ d₂ c₂ →
           n₁ ℤ.* + suc d₂ ≡ n₂ ℤ.* + suc d₁ →
           (n₁ ÷ suc d₁) {c₁} ≡ (n₂ ÷ suc d₂) {c₂}
  helper n₁ d₁ c₁ n₂ d₂ c₂ eq
    with Poset.antisym ℕDiv.poset 1+d₁∣1+d₂ 1+d₂∣1+d₁
    where
    1+d₁∣1+d₂ : suc d₁ ∣ suc d₂
    1+d₁∣1+d₂ = ℤDiv.coprime-divisor (+ suc d₁) n₁ (+ suc d₂)
                  (C.sym $ toWitness c₁) $
                  ℕDiv.divides ℤ.∣ n₂ ∣ (begin
                    ℤ.∣ n₁ ℤ.* + suc d₂ ∣  ≡⟨ cong ℤ.∣_∣ eq ⟩
                    ℤ.∣ n₂ ℤ.* + suc d₁ ∣  ≡⟨ ℤ.abs-*-commute n₂ (+ suc d₁) ⟩
                    ℤ.∣ n₂ ∣ ℕ.* suc d₁    ∎)

    1+d₂∣1+d₁ : suc d₂ ∣ suc d₁
    1+d₂∣1+d₁ = ℤDiv.coprime-divisor (+ suc d₂) n₂ (+ suc d₁)
                  (C.sym $ toWitness c₂) $
                  ℕDiv.divides ℤ.∣ n₁ ∣ (begin
                    ℤ.∣ n₂ ℤ.* + suc d₁ ∣  ≡⟨ cong ℤ.∣_∣ (P.sym eq) ⟩
                    ℤ.∣ n₁ ℤ.* + suc d₂ ∣  ≡⟨ ℤ.abs-*-commute n₁ (+ suc d₂) ⟩
                    ℤ.∣ n₁ ∣ ℕ.* suc d₂    ∎)

  helper n₁ d c₁ n₂ .d c₂ eq | refl with ℤ.cancel-*-right
                                           n₁ n₂ (+ suc d) (λ ()) eq
  helper n  d c₁ .n .d c₂ eq | refl | refl with Bool.proof-irrelevance c₁ c₂
  helper n  d c  .n .d .c eq | refl | refl | refl = refl

------------------------------------------------------------------------
-- Equality is decidable

infix 4 _≟_

_≟_ : Decidable {A = ℚ} _≡_
p ≟ q with ℚ.numerator p ℤ.* ℚ.denominator q ℤ.≟
           ℚ.numerator q ℤ.* ℚ.denominator p
p ≟ q | yes pq≃qp = yes (≃⇒≡ pq≃qp)
p ≟ q | no ¬pq≃qp = no (¬pq≃qp ∘ ≡⇒≃)

------------------------------------------------------------------------
-- Ordering

infix 4 _≤_ _≤?_

data _≤_ : ℚ → ℚ → Set where
  *≤* : ∀ {p q} →
        ℚ.numerator p ℤ.* ℚ.denominator q ℤ.≤
        ℚ.numerator q ℤ.* ℚ.denominator p →
        p ≤ q

drop-*≤* : ∀ {p q} → p ≤ q →
           ℚ.numerator p ℤ.* ℚ.denominator q ℤ.≤
           ℚ.numerator q ℤ.* ℚ.denominator p
drop-*≤* (*≤* pq≤qp) = pq≤qp

_≤?_ : Decidable _≤_
p ≤? q with ℚ.numerator p ℤ.* ℚ.denominator q ℤ.≤?
            ℚ.numerator q ℤ.* ℚ.denominator p
p ≤? q | yes pq≤qp = yes (*≤* pq≤qp)
p ≤? q | no ¬pq≤qp = no (λ { (*≤* pq≤qp) → ¬pq≤qp pq≤qp })

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier         = ℚ
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = P.isEquivalence
                  ; reflexive     = refl′
                  ; trans         = trans
                  }
                ; antisym = antisym
              }
          ; total = total
          }
      ; _≟_  = _≟_
      ; _≤?_ = _≤?_
      }
  }
  where
  module ℤO = DecTotalOrder ℤ.decTotalOrder

  refl′ : _≡_ ⇒ _≤_
  refl′ refl = *≤* ℤO.refl

  trans : Transitive _≤_
  trans {i = p} {j = q} {k = r} (*≤* le₁) (*≤* le₂)
    = *≤* (ℤ.cancel-*-+-right-≤ _ _ _
            (lemma
              (ℚ.numerator p) (ℚ.denominator p)
              (ℚ.numerator q) (ℚ.denominator q)
              (ℚ.numerator r) (ℚ.denominator r)
              (ℤ.*-+-right-mono (ℚ.denominator-1 r) le₁)
              (ℤ.*-+-right-mono (ℚ.denominator-1 p) le₂)))
    where
    open Algebra.CommutativeRing ℤ.commutativeRing

    lemma : ∀ n₁ d₁ n₂ d₂ n₃ d₃ →
            n₁ ℤ.* d₂ ℤ.* d₃ ℤ.≤ n₂ ℤ.* d₁ ℤ.* d₃ →
            n₂ ℤ.* d₃ ℤ.* d₁ ℤ.≤ n₃ ℤ.* d₂ ℤ.* d₁ →
            n₁ ℤ.* d₃ ℤ.* d₂ ℤ.≤ n₃ ℤ.* d₁ ℤ.* d₂
    lemma n₁ d₁ n₂ d₂ n₃ d₃
      rewrite *-assoc n₁ d₂ d₃
            | *-comm d₂ d₃
            | sym (*-assoc n₁ d₃ d₂)
            | *-assoc n₃ d₂ d₁
            | *-comm d₂ d₁
            | sym (*-assoc n₃ d₁ d₂)
            | *-assoc n₂ d₁ d₃
            | *-comm d₁ d₃
            | sym (*-assoc n₂ d₃ d₁)
            = ℤO.trans

  antisym : Antisymmetric _≡_ _≤_
  antisym (*≤* le₁) (*≤* le₂) = ≃⇒≡ (ℤO.antisym le₁ le₂)

  total : Total _≤_
  total p q =
    [ inj₁ ∘′ *≤* , inj₂ ∘′ *≤* ]′
      (ℤO.total (ℚ.numerator p ℤ.* ℚ.denominator q)
                (ℚ.numerator q ℤ.* ℚ.denominator p))

------------------------------------------------------------------------------
-- A few constants and some small tests

0ℚ 1ℚ : ℚ
0ℚ = + 0 ÷ 1
1ℚ = + 1 ÷ 1

private

  p₀ p₁ p₂ p₃ : ℚ
  p₀ = + 1 ÷ 2
  p₁ = + 1 ÷ 3
  p₂ = -[1+ 2 ] ÷ 4
  p₃ = + 3 ÷ 4

  test₀ = show p₂
  test₁ = show (- p₂)
  test₂ = show (1/ p₂)
  test₃ = show (p₀ + p₀)
  test₄ = show (p₁ * p₂)
