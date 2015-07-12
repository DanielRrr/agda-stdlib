------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

module Data.Rational where

import Data.Integer.Multiplication.Properties as Mul
open import Algebra using (module CommutativeMonoid)
import Data.Sign as S
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
import Data.Bool.Properties as Bool
open import Function
open import Data.Product
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; _◃_; sign)
import Data.Integer.Properties as ℤ
open import Data.Nat.GCD
open import Data.Nat.Divisibility as ℕDiv using (_∣_; divides; quotient)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Sum
open import Data.String using (String; _++_)
import Level
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core using (_≢_)
open import Relation.Binary.PropositionalEquality as P using 
  (_≡_; refl; subst; cong; cong₂)
open import Data.Integer.Properties using (cancel-*-right)
open P.≡-Reasoning
open CommutativeMonoid Mul.commutativeMonoid
  using ()
  renaming (assoc to *-assoc; comm to *-comm; identity to *-identity
           ; isCommutativeMonoid to *-isCommutativeMonoid
           ; isMonoid to *-isMonoid
           )

infix  8 -_ 1/_
infixl 7   _*_ _/_
infixl 6  _+_ _-_

------------------------------------------------------------------------
-- The definition

--Rational numbers 
--Note that we do not require the arguments to be given in their reduced form

record ℚ : Set where
  constructor _÷suc_
  field
    numerator     : ℤ
    denominator-1 : ℕ

  denominator : ℤ
  denominator = + suc denominator-1

infixl 7 _÷_

_÷_ : (n : ℤ) (d : ℕ) -> {≢0 : False (ℕ._≟_ d 0)} -> ℚ
(n ÷ 0) {()}
n ÷ (suc d) = n ÷suc d

------------------------------------------------------------------------
--  Functions for reducing rational numbers to their coprime form

-- normalize takes two natural numbers, say 6 and 21 and their gcd 3, and
-- returns them normalized as 2 and 7
normalize : {m n g : ℕ} → 
  {n≢0 : False (ℕ._≟_ n 0)} → {g≢0 : False (ℕ._≟_ g 0)} →
            GCD m n g → ℚ
normalize {m} {n} {0} {_} {()} _
normalize {m} {.0} {ℕ.suc g} {()} {_}
  (GCD.is (divides p m≡pg' , divides 0 refl) _)
normalize {m} {n} {ℕ.suc g} {_} {_}
  (GCD.is (divides p m≡pg' , divides (suc q) n≡qg') _) =
    ((+ p) ÷suc q)

--gcd that gives a proof that g is NonZero if one of its inputs are NonZero
gcd≢0 : (m n : ℕ) → {n≢0 : False (ℕ._≟_ n 0)} → ∃ λ d → 
  GCD m n d × (False (ℕ._≟_ d 0))
gcd≢0 m n {m≢0} with gcd m n
gcd≢0 m n {m≢0} | (0 , GCD.is (_ , 0n) _) with ℕDiv.0∣⇒≡0 0n
gcd≢0 m .0 {()} | (0 , GCD.is (_ , 0n) _) | refl
gcd≢0 m n {_} | (ℕ.suc d , G) = (ℕ.suc d , G , tt)

--Unary negation
-_ : ℚ → ℚ
- n ÷suc d = (ℤ.- n) ÷suc d

--Reduces a given rational number to its coprime form
reduce : ℚ -> ℚ
reduce ((+ 0) ÷suc d) = (+ 0 ÷ 1)
reduce (-[1+ n ] ÷suc d) = 
  - normalize {ℤ.∣ -[1+ n ] ∣} {suc d} {proj₁ (gcd≢0 (suc n) (suc d) {_})} {_}
  {proj₂ (proj₂ (gcd≢0 (suc n) (suc d) {_}))} 
  (proj₁( proj₂ (gcd≢0 (suc n) (suc d) {_})))
reduce ((+ n) ÷suc d) = 
  normalize {ℤ.∣ + n ∣} {suc d} {proj₁ (gcd≢0 n (suc d) {_})} {_} 
  {proj₂ (proj₂ (gcd≢0 n (suc d) {_}))} 
  (proj₁ (proj₂ (gcd≢0 n (suc d) {_})))

------------------------------------------------------------------------------
-- Operations on rationals: reciprocal, multiplication, addition

-- reciprocal: requires a proof that the numerator is not zero

1/_ : (p : ℚ) → {≢0 : False (ℕ._≟_ (ℤ.∣ ℚ.numerator p ∣) 0)} → ℚ
1/_ ((+ 0) ÷suc d) {()}
1/_ ((+ suc n) ÷suc d) = (+ suc d) ÷suc n
1/_ (-[1+ n ] ÷suc d) = -[1+ d ] ÷suc n

--Multiplication and addition

_*_ : ℚ -> ℚ -> ℚ
(n₁ ÷suc d₁) * (n₂ ÷suc d₂) = ((n₁ ℤ.* n₂) ÷ (suc d₁ ℕ.* suc d₂))

_+_ :  ℚ -> ℚ -> ℚ
(n₁ ÷suc d₁) + (n₂ ÷suc d₂) =  ((n₁ ℤ.* + (suc d₂)) ℤ.+ (n₂ ℤ.* + (suc  d₁))) 
  ÷ ((suc d₁) ℕ.* (suc d₂))

 -- subtraction and division

_-_ : ℚ → ℚ → ℚ
p₁ - p₂ = p₁ + (- p₂)

_/_ : (p₁ p₂ : ℚ) → {≢0 : False (ℕ._≟_ ℤ.∣ ℚ.numerator p₂ ∣ 0)} → ℚ
_/_ p₁ p₂ {≢0} = p₁ * (1/_ p₂ {≢0})


--absolute value
∣_∣ : ℚ -> ℚ
∣ n ÷suc d ∣ = (+ ℤ.∣ n ∣) ÷suc d

-- conventional printed representation

show : ℚ → String
show p = ℤ.show (ℚ.numerator p) ++ "/" ++ ℕshow (ℕ.suc (ℚ.denominator-1 p))

------------------------------------------------------------------------
-- Equality

-- We define an equality relation on rational numbers in the conventional way

infix 4 _≃_

_≃_ : Rel ℚ Level.zero
p ≃ q = numerator p ℤ.* (+ suc (denominator-1 q)) ≡
        numerator q ℤ.* (+ suc (denominator-1 p))
  where open ℚ

--This is an equivalence relation
isEquivalence : IsEquivalence _≃_
isEquivalence = record {
  refl = refl ;
  sym = P.sym ;
  trans = λ {a}{b}{c} -> trans {a}{b}{c}
  }
    where
    trans : Transitive _≃_
    trans {a ÷suc b} {f ÷suc g} {x ÷suc y} ag≃fb fy≃xg = 
      cancel-*-right (a ℤ.* (+ suc y)) (x ℤ.* (+ suc b)) (+ suc g) (λ {()}) 
        (P.trans ayg≃fby fby≃xbg)
      where
        agy≃fby : (a ℤ.* + suc g ℤ.* + suc y ≡ f ℤ.* + suc b ℤ.* + suc y)
        agy≃fby = cong (λ j -> (j ℤ.* + suc y)) (ag≃fb)
        ayg≃fby : (a ℤ.* + suc y ℤ.* + suc g ≡ f ℤ.* + suc b ℤ.* + suc y)
        ayg≃fby = P.trans (*-assoc a (+ suc y) (+ suc g)) 
          (P.trans (cong (λ j -> (a ℤ.* j )) (*-comm (+ suc y) (+ suc g))) 
            (P.trans (P.sym (*-assoc a (+ suc g) (+ suc y))) agy≃fby))
        fyb≃xgb : (f ℤ.* + suc y ℤ.* + suc b ≡ x ℤ.* + suc g ℤ.* + suc b)
        fyb≃xgb = cong (λ j -> j ℤ.* (+ suc b)) fy≃xg
        fby≃xgb : (f ℤ.* + suc b ℤ.* + suc y ≡ x ℤ.* + suc g ℤ.* + suc b)
        fby≃xgb = P.trans (*-assoc f (+ suc b) (+ suc y)) 
          (P.trans (cong (λ j -> (f ℤ.* j )) (*-comm (+ suc b) (+ suc y))) 
            (P.trans (P.sym (*-assoc f (+ suc y) (+ suc b))) fyb≃xgb))
        fby≃xbg : (f ℤ.* + suc b ℤ.* + suc y ≡ x ℤ.* + suc b ℤ.* + suc g)
        fby≃xbg = P.trans (P.trans (fby≃xgb) (*-assoc x (+ suc g) (+ suc b))) 
          (P.trans (cong (λ j -> (x ℤ.* j)) (*-comm (+ suc g) (+ suc b))) 
            (P.sym (*-assoc x (+ suc b) (+ suc g))))


------------------------------------------------------------------------
--Equality is decidable

infix 4 _≟_

_≟_ : Decidable {A = ℚ} _≃_
p ≟ q with ℚ.numerator p ℤ.* (+ suc (ℚ.denominator-1 q)) ℤ.≟
            ℚ.numerator q ℤ.* (+ suc (ℚ.denominator-1 p))
p ≟ q | yes pq≃qp = yes (pq≃qp)
p ≟ q | no ¬pq≃qp = no (¬pq≃qp)

--------------------------------------------------------------------------
 -- Ordering

infix 4 _≤_ _≤?_

data _≤_ : ℚ → ℚ → Set where
  *≤* : ∀ {p q} →
        ℚ.numerator p ℤ.* (+ suc (ℚ.denominator-1 q)) ℤ.≤
        ℚ.numerator q ℤ.* (+ suc (ℚ.denominator-1 p)) →
        p ≤ q

drop-*≤* : ∀ {p q} → p ≤ q →
           ℚ.numerator p ℤ.* (+ suc (ℚ.denominator-1 q)) ℤ.≤
           ℚ.numerator q ℤ.* (+ suc (ℚ.denominator-1 p))
drop-*≤* (*≤* pq≤qp) = pq≤qp

_≤?_ : Decidable _≤_
p ≤? q with ℚ.numerator p ℤ.* (+ suc (ℚ.denominator-1 q)) ℤ.≤?
            ℚ.numerator q ℤ.* (+ suc (ℚ.denominator-1 p))
p ≤? q | yes pq≤qp = yes (*≤* pq≤qp)
p ≤? q | no ¬pq≤qp = no (λ { (*≤* pq≤qp) → ¬pq≤qp pq≤qp })

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier         = ℚ
  ; _≈_             = _≃_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = isEquivalence
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

  refl′ : _≃_ ⇒ _≤_
  refl′ p = *≤* (reflexive p)
    where
      open DecTotalOrder ℤ.decTotalOrder using (reflexive)

  trans : Transitive _≤_
  trans {i = p} {j = q} {k = r} (*≤* le₁) (*≤* le₂)
    = *≤* (ℤ.cancel-*-+-right-≤ _ _ _
            (lemma
              (ℚ.numerator p) ((+ suc (ℚ.denominator-1 p)))
              (ℚ.numerator q) ((+ suc (ℚ.denominator-1 q)))
              (ℚ.numerator r) ((+ suc (ℚ.denominator-1 r)))
              (ℤ.*-+-right-mono (ℚ.denominator-1 r) le₁)
              (ℤ.*-+-right-mono (ℚ.denominator-1 p) le₂)))
    where

    lemma : ∀ n₁ d₁ n₂ d₂ n₃ d₃ →
            n₁ ℤ.* d₂ ℤ.* d₃ ℤ.≤ n₂ ℤ.* d₁ ℤ.* d₃ →
            n₂ ℤ.* d₃ ℤ.* d₁ ℤ.≤ n₃ ℤ.* d₂ ℤ.* d₁ →
            n₁ ℤ.* d₃ ℤ.* d₂ ℤ.≤ n₃ ℤ.* d₁ ℤ.* d₂
    lemma n₁ d₁ n₂ d₂ n₃ d₃
      rewrite *-assoc n₁ d₂ d₃
            | *-comm d₂ d₃
            | P.sym (*-assoc n₁ d₃ d₂)
            | *-assoc n₃ d₂ d₁
            | *-comm d₂ d₁
            | P.sym (*-assoc n₃ d₁ d₂)
            | *-assoc n₂ d₁ d₃
            | *-comm d₁ d₃
            | P.sym (*-assoc n₂ d₃ d₁)
            = ℤO.trans

  antisym : Antisymmetric _≃_ _≤_
  antisym (*≤* le₁) (*≤* le₂) = (ℤO.antisym le₁ le₂)

  total : Total _≤_
  total p q =
    [ inj₁ ∘′ *≤* , inj₂ ∘′ *≤* ]′
      (ℤO.total (ℚ.numerator p ℤ.* (+ suc (ℚ.denominator-1 q)))
                (ℚ.numerator q ℤ.* (+ suc (ℚ.denominator-1 p))))
