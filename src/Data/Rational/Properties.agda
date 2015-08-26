module Data.Rational.Properties where

open import Function
open import Data.Sum
open import Data.Empty
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
open import Data.Rational as ℚ using (ℚ; -_ ; _*_; _÷suc_;
  _-_; _+_; ∣_∣; decTotalOrder; _≤_; *≤* ; _≤?_; _÷_; _≃_;
  isEquivalence; drop-*≤*)
open import Level renaming (zero to Levelzero; suc to Levelsuc)
open import Data.Integer as ℤ using (decTotalOrder; ℤ; +_ ;
  -[1+_]; _≤?_; _⊖_; ◃-cong; ◃-left-inverse; sign; drop‿+≤+) renaming 
  (_-_ to ℤ_-_; _+_ to _ℤ+_; _*_ to  _ℤ*_;_≤_ to ℤ_≤_)
open import Data.Nat as ℕ using (ℕ; suc; zero; pred; compare;
  _<_; _∸_; s≤s; z≤n; _≥_; decTotalOrder)
    renaming (_≤_ to ℕ_≤_; _≤?_ to _≤??_)
open import Data.Nat.Properties.Simple using (+-comm; +-suc;
  *-comm; +-right-identity; +-*-suc)
open import Relation.Binary.Core
open import Data.Nat.Properties using (m≤m+n; _+-mono_; ≤-steps;
  ≤-step; ≰⇒>; ≤⇒pred≤; ≤pred⇒≤; pred-mono; n≤1+n; _*-mono_; 1+n≰n)
import Relation.Binary.PreorderReasoning as Pre
import Data.Integer.Addition.Properties as Add
open import Relation.Binary.PropositionalEquality.Core
  using (trans; subst)
open import Algebra
  using (module CommutativeRing; module CommutativeMonoid)
open import Data.Integer.Properties using (commutativeRing; abs-◃;
  *-+-right-mono; cancel-*-+-right-≤; n⊖n≡0)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; 
  subst; cong; cong₂; subst₂)
open import Data.Product
open import Relation.Binary using (module DecTotalOrder)
open CommutativeRing commutativeRing
  using ()
  renaming (distrib to ℤdistrib; +-assoc to ℤ+-assoc; *-assoc to ℤ*-assoc; *-comm to ℤ*-comm; +-comm to ℤ+-comm; *-identity to ℤ*-identity)
open CommutativeMonoid Add.commutativeMonoid
  using ()
  renaming (identity to ℤ+-identity)
open DecTotalOrder ℕ.decTotalOrder using () renaming (refl to ≤-refl)

--This module contains various lemmas and additional functions on
--rational numbers
_⁻¹ : (n : ℕ) -> {≢0 : False (ℕ._≟_ n 0)} -> ℚ
(n ⁻¹) {≢0} = ((+ 1) ÷ n) {≢0}

--Lemmas helping to show symmetry of the equivalence relation 
--defined on the real numbers

⊖-swap : ∀ a b → a ℤ.⊖ b ≡ ℤ.- (b ℤ.⊖ a)

⊖-swap zero zero = refl
⊖-swap zero (suc n) = refl
⊖-swap (suc n) zero = refl
⊖-swap (suc n) (suc n₁) = ⊖-swap n n₁

ℤ-swap : (a b : ℤ) -> (ℤ.- (a ℤ.- b) ≡ b ℤ.- a)

ℤ-swap -[1+ n ] -[1+ n₁ ] = P.sym (⊖-swap n n₁)
ℤ-swap -[1+ n ] (+ zero) = refl
ℤ-swap -[1+ n ] (+ suc n₁) = trans (cong (λ a -> + suc (suc a)) 
  (+-comm n n₁)) (cong ℤ.+_ (P.sym (+-suc (suc n₁) n)))
ℤ-swap (+ zero) -[1+ n₁ ] = refl
ℤ-swap (+ suc n) -[1+ n₁ ] = cong -[1+_] (+-comm n (suc n₁))
ℤ-swap (+ zero) (+ zero) = refl
ℤ-swap (+ zero) (+ suc n₁) = cong ℤ.+_ (P.sym (+-right-identity (suc n₁)))
ℤ-swap (+ suc n) (+ zero) = cong -[1+_] (+-right-identity n)
ℤ-swap (+ suc n) (+ suc n₁) = P.sym (⊖-swap n₁ n)

ℚ-swap : (x y : ℚ) -> (- (y - x) ≡ x - y)

ℚ-swap (-[1+ n₁ ] ÷suc d₁) (-[1+ n₂ ] ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (-[1+ n₂ ] ℤ.* + suc d₁) (-[1+ n₁ ] ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
ℚ-swap (-[1+ n₁ ] ÷suc d₁) ((+ zero) ÷suc d₂) = 
  cong (λ a -> (-[1+ n₁ ] ℤ.* (+ suc d₂)) ℚ.÷suc (pred a))
  (*-comm (suc d₂) (suc d₁))
ℚ-swap (-[1+ n₁ ] ÷suc d₁) ((+ suc n₂) ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (+ suc n₂ ℤ.* + suc d₁) (-[1+ n₁ ] ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ zero) ÷suc d₁) (-[1+ n₂ ] ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (-[1+ n₂ ] ℤ.* + suc d₁) (+ zero ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ suc n₁) ÷suc d₁) (-[1+ n₂ ] ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (-[1+ n₂ ] ℤ.* + suc d₁) (+ suc n₁ ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ zero) ÷suc d₁) ((+ zero) ÷suc d₂) = 
  cong (λ a -> ((+ zero) ÷suc (pred a)))
  (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ zero) ÷suc d₁) ((+ suc n₂) ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (+ suc n₂ ℤ.* + suc d₁) (+ zero ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ suc n) ÷suc d₁) ((+ zero) ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (+ zero ℤ.* + suc d₁) (+ suc n ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ suc n₁) ÷suc d₁) ((+ suc n₂) ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (+ suc n₂ ℤ.* + suc d₁) (+ suc n₁ ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))

ℚabs₁ : (x : ℚ) -> (∣ ℚ.- x ∣ ≡ ∣ x ∣)
ℚabs₁ (-[1+ n ] ÷suc d₁) = refl
ℚabs₁ ((+ zero) ÷suc d₁) = refl
ℚabs₁ ((+ suc n) ÷suc d₁) = refl

ℚabs₂ : (x y : ℚ) -> (∣ x - y ∣ ≡ ∣ y - x ∣)
ℚabs₂ x y = trans (cong ∣_∣ (P.sym (ℚ-swap x y) ))(ℚabs₁ (y - x))


--Since the we have defined rationals without requiring coprimality, 
--our equivalence relation ≈ is not synonymous with ≡ and therefore 
--we cannot use subst or cong to modify expressions. 
--Instead, we have to show that every function defined on rationals 
--preserves the equality relation.
+-exist :  _+_ Preserves₂ _≃_ ⟶ _≃_ ⟶ _≃_
+-exist {p}{q}{x}{y} pq xy =  begin 
  (pn ℤ.* xd ℤ.+ xn ℤ.* pd) ℤ.* (qd ℤ.* yd) 
  ≡⟨ proj₂ ℤdistrib (qd ℤ.* yd) (pn ℤ.* xd) (xn ℤ.* pd)   ⟩
  pn ℤ.* xd ℤ.* (qd ℤ.* yd) ℤ.+ xn ℤ.* pd ℤ.* (qd ℤ.* yd) 
  ≡⟨ cong₂ ℤ._+_ (ℤ*-assoc pn xd (qd ℤ.* yd)) (ℤ*-assoc xn pd (qd ℤ.* yd)) ⟩
  pn ℤ.* (xd ℤ.* (qd ℤ.* yd)) ℤ.+ xn ℤ.* (pd ℤ.* (qd ℤ.* yd)) 
  ≡⟨ cong₂ (λ a b -> pn ℤ.* a ℤ.+ xn ℤ.* (pd ℤ.* b)) 
    (P.sym (ℤ*-assoc xd qd yd)) (ℤ*-comm qd yd) ⟩
  pn ℤ.* (xd ℤ.* qd ℤ.* yd) ℤ.+ xn ℤ.* (pd ℤ.* (yd ℤ.* qd)) 
  ≡⟨ cong₂ (λ a b -> pn ℤ.* (a ℤ.* yd) ℤ.+ xn ℤ.* b) 
    (ℤ*-comm xd qd) (P.sym (ℤ*-assoc pd yd qd)) ⟩
  pn ℤ.* (qd ℤ.* xd ℤ.* yd) ℤ.+ xn ℤ.* (pd ℤ.* yd ℤ.* qd) 
  ≡⟨ cong₂ (λ a b -> pn ℤ.* a ℤ.+ xn ℤ.* (b ℤ.* qd)) 
    (ℤ*-assoc qd xd yd) (ℤ*-comm pd yd) ⟩
  pn ℤ.* (qd ℤ.* (xd ℤ.* yd)) ℤ.+ xn ℤ.* (yd ℤ.* pd ℤ.* qd) 
  ≡⟨ cong₂ (λ a b -> a ℤ.+ xn ℤ.* b) 
    (P.sym (ℤ*-assoc pn qd (xd ℤ.* yd))) (ℤ*-assoc yd pd qd) ⟩
  pn ℤ.* qd ℤ.* (xd ℤ.* yd) ℤ.+ xn ℤ.* (yd ℤ.* (pd ℤ.* qd)) 
  ≡⟨ cong₂ (λ a b -> a ℤ.* (xd ℤ.* yd) ℤ.+ b) pq  
    (P.sym (ℤ*-assoc xn yd (pd ℤ.* qd))) ⟩
  qn ℤ.* pd ℤ.* (xd ℤ.* yd) ℤ.+ xn ℤ.* yd ℤ.* (pd ℤ.* qd) 
  ≡⟨ cong₂ (λ a b -> a ℤ.+ b ℤ.* (pd ℤ.* qd)) 
    (ℤ*-assoc qn pd (xd ℤ.* yd)) xy ⟩
  qn ℤ.* (pd ℤ.* (xd ℤ.* yd)) ℤ.+ yn ℤ.* xd ℤ.* (pd ℤ.* qd) 
  ≡⟨ cong₂ (λ a b -> qn ℤ.* (pd ℤ.* a) ℤ.+ yn ℤ.* xd ℤ.* b) 
    (ℤ*-comm xd yd) (ℤ*-comm pd qd) ⟩
  qn ℤ.* (pd ℤ.* (yd ℤ.* xd)) ℤ.+ yn ℤ.* xd ℤ.* (qd ℤ.* pd) 
  ≡⟨ cong₂ (λ a b -> qn ℤ.* a ℤ.+ b) 
    (P.sym (ℤ*-assoc pd yd xd )) (ℤ*-assoc yn xd (qd ℤ.* pd)) ⟩
  qn ℤ.* (pd ℤ.* yd ℤ.* xd) ℤ.+ yn ℤ.* (xd ℤ.* (qd ℤ.* pd)) 
  ≡⟨ cong₂ (λ a b -> qn ℤ.* (a ℤ.* xd) ℤ.+ yn ℤ.* b) 
    (ℤ*-comm pd yd) (P.sym (ℤ*-assoc xd qd pd )) ⟩
  qn ℤ.* (yd ℤ.* pd ℤ.* xd) ℤ.+ yn ℤ.* (xd ℤ.* qd ℤ.* pd) 
  ≡⟨ cong₂ (λ a b -> qn ℤ.* a ℤ.+ yn ℤ.* (b ℤ.* pd)) 
    (ℤ*-assoc yd pd xd) (ℤ*-comm xd qd) ⟩
  qn ℤ.* (yd ℤ.* (pd ℤ.* xd)) ℤ.+ yn ℤ.* (qd ℤ.* xd ℤ.* pd) 
  ≡⟨ cong₂ (λ a b -> a ℤ.+ yn ℤ.* b) 
    (P.sym (ℤ*-assoc qn yd (pd ℤ.* xd))) (ℤ*-assoc qd xd pd) ⟩
  qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* (qd ℤ.* (xd ℤ.* pd)) 
  ≡⟨ cong (λ a -> qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* (qd ℤ.* a)) 
    (ℤ*-comm xd pd) ⟩
  qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* (qd ℤ.* (pd ℤ.* xd)) 
  ≡⟨ cong (λ a -> qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ a) 
    (P.sym (ℤ*-assoc yn qd (pd ℤ.* xd))) ⟩
  qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* qd ℤ.* (pd ℤ.* xd) 
  ≡⟨ P.sym (proj₂ ℤdistrib (pd ℤ.* xd) (qn ℤ.* yd) (yn ℤ.* qd)) ⟩
  (qn ℤ.* yd ℤ.+ yn ℤ.* qd) ℤ.* (pd ℤ.* xd)
        ∎
         where
           open P.≡-Reasoning
           pn = ℚ.numerator p
           pd = ℚ.denominator p
           qn = ℚ.numerator q
           qd = ℚ.denominator q
           xn = ℚ.numerator x
           xd = ℚ.denominator x
           yn = ℚ.numerator y
           yd = ℚ.denominator y

+-red₁ : (n : ℕ) -> 
  ((+ 1) ÷suc (suc (n ℕ.+ n)) ℚ.+ 
  (+ 1) ÷suc (suc (n ℕ.+ n)) ℚ.≃ (+ 1) ÷suc n)
+-red₁ n = begin 
  ((+ 1) ℤ.* k ℤ.+ (+ 1) ℤ.* k) ℤ.* + suc n 
  ≡⟨ cong (λ a -> ((a ℤ.+ a) ℤ.* + suc n)) (proj₁ ℤ*-identity k) ⟩
  (k ℤ.+ k) ℤ.* + suc n 
  ≡⟨ cong (λ a -> a ℤ.* + suc n) (P.sym (lem k)) ⟩
  (+ 2) ℤ.* k ℤ.* (+ suc n) 
  ≡⟨ cong (λ a -> a ℤ.* + suc n) (ℤ*-comm (+ 2) k) ⟩
  k ℤ.* (+ 2) ℤ.* (+ suc n) 
  ≡⟨ ℤ*-assoc k (+ 2) (+ suc n) ⟩
  k ℤ.* ((+ 2) ℤ.* (+ suc n)) 
  ≡⟨ cong (λ a -> k ℤ.* a) (lem (+ suc n)) ⟩
  k ℤ.* (+ suc (n ℕ.+ suc n)) 
  ≡⟨ cong (λ a -> k ℤ.* + suc a) (+-comm n (suc n)) ⟩
  k ℤ.* k ≡⟨ P.sym (proj₁ ℤ*-identity (k ℤ.* k)) ⟩
  (+ 1) ℤ.* (k ℤ.* k)
  ∎
    where
      open P.≡-Reasoning
      k = + suc (suc (n ℕ.+ n))
      lem : (j : ℤ) -> ((+ 2) ℤ.* j ≡ j ℤ.+ j)
      lem j = trans (proj₂ ℤdistrib j (+ 1) (+ 1)) 
        (cong₂ ℤ._+_ (proj₁ ℤ*-identity j) (proj₁ ℤ*-identity j)) 

+-red₂ : (n : ℕ) -> 
       (((+ 1) ÷suc (suc ((suc (n ℕ.+ n)) ℕ.+ (suc (n ℕ.+ n)))) +
       (+ 1) ÷suc (suc ((suc (n ℕ.+ n)) ℕ.+ (suc (n ℕ.+ n))))) 
      + 
      ((+ 1) ÷suc (suc ((suc (n ℕ.+ n)) ℕ.+ (suc (n ℕ.+ n)))) +
      (+ 1) ÷suc (suc ((suc (n ℕ.+ n)) ℕ.+ (suc (n ℕ.+ n))))) 
      ℚ.≃ ((+ 1) ÷suc n))
+-red₂ n = IsEquivalence.trans ℚ.isEquivalence {start} {middle} {end} 
  (+-exist {1÷k + 1÷k}{1÷j}{1÷k + 1÷k}{1÷j} (+-red₁ j) (+-red₁ j)) 
    (+-red₁ n)
  where
    j = suc (n ℕ.+ n)
    k = suc (j ℕ.+ j)
    1÷j = (+ 1) ÷suc j
    1÷k = (+ 1) ÷suc k
    start = (1÷k + 1÷k) + (1÷k + 1÷k)
    middle = 1÷j + 1÷j
    end = (+ 1) ÷suc n

ℚ≤lem : {m n : ℕ} -> ((+ 1) ÷suc (m ℕ.+ n) ≤ (+ 1) ÷suc m)
ℚ≤lem {m}{n} =  *≤* (ℤ.+≤+ (ℕ.s≤s ((m≤m+n m n) +-mono (z≤n))))

_ℤ+-mono_ :  ℤ._+_ Preserves₂ ℤ._≤_ ⟶ ℤ._≤_ ⟶ ℤ._≤_
ℤ.-≤+ ℤ+-mono ℤ.-≤+ = ℤ.-≤+
ℤ.-≤+ {n} {zero} ℤ+-mono ℤ.-≤- {m} {zero} m₁≤n₁ = ℤ.-≤- z≤n
ℤ.-≤+ ℤ+-mono ℤ.-≤- {zero} {suc n} ()
ℤ.-≤+ {zero} {zero} ℤ+-mono ℤ.-≤- {suc m} {suc n} m₁≤n₁ =
  ℤ.-≤- (z≤n {suc zero} +-mono m₁≤n₁)
ℤ.-≤+ {m} {suc n} ℤ+-mono ℤ.-≤- {m₁} {zero} m₁≤n₁ = ℤ.-≤+
ℤ.-≤+ {zero} {suc n} ℤ+-mono ℤ.-≤- {suc m} {suc n₁} (s≤s m₁≤n₁) =
  ℤ.-≤+ {suc zero} {n} ℤ+-mono ℤ.-≤- {m} {n₁} (m₁≤n₁)
ℤ.-≤+ {suc m} {zero} ℤ+-mono ℤ.-≤- {suc m₁} {suc n} m₁≤n₁ =
  ℤ.-≤- (≤-steps (suc (suc m)) m₁≤n₁)
ℤ.-≤+ {suc m} {suc n} ℤ+-mono ℤ.-≤- {suc m₁} {suc n₁} (s≤s m₁≤n₁) =
  ℤ.-≤+ {suc m} {n} ℤ+-mono ℤ.-≤- {suc m₁} {n₁} (≤-step m₁≤n₁)
ℤ.-≤+ ℤ+-mono ℤ.+≤+ {zero} {n₁} m≤n = ℤ.-≤+
ℤ.-≤+ ℤ+-mono ℤ.+≤+ {suc m₁} {zero} () 
ℤ.-≤+ {zero} {n} ℤ+-mono ℤ.+≤+ {suc m₁} {suc n₁} (s≤s m≤n) =
  ℤ.+≤+ (≤-steps n (≤-step m≤n))
ℤ.-≤+ {suc m} {n} ℤ+-mono ℤ.+≤+ {suc m₁} {suc n₁} (s≤s m≤n) =
  ℤ.-≤+ {m}{n} ℤ+-mono ℤ.+≤+ {m₁}{suc n₁} (≤-step m≤n)
ℤ.-≤- {m} {zero} n≤m ℤ+-mono ℤ.-≤+ {n₁} {zero} = ℤ.-≤- z≤n
ℤ.-≤- {m} {zero} n≤m ℤ+-mono ℤ.-≤+ {n₁} {suc n} = ℤ.-≤+
ℤ.-≤- {zero} {suc n}() ℤ+-mono ℤ.-≤+
ℤ.-≤- {suc m} {suc n} n≤m ℤ+-mono ℤ.-≤+ {zero} {zero} =
  ℤ.-≤- (subst₂ (λ a b -> a ℕ.≤ suc b) (+-right-identity (suc n))
    (+-suc m zero) (n≤m +-mono z≤n {suc zero}))
ℤ.-≤- {suc m} {suc n} (s≤s n≤m) ℤ+-mono ℤ.-≤+ {m₁} {suc n₁} =
  ℤ.-≤- {suc m} {n} (≤-step n≤m) ℤ+-mono ℤ.-≤+ {m₁}{n₁}
ℤ.-≤- {suc m} {suc n} (s≤s n≤m) ℤ+-mono ℤ.-≤+ {m₁} {zero} =
  ℤ.-≤- (subst (λ a -> suc n ℕ.≤ suc (suc a)) (+-comm m₁ m)
    (s≤s (≤-step (≤-steps m₁ n≤m))))
ℤ.-≤- {m} {n}  n≤m ℤ+-mono ℤ.-≤-  n≤m₁ = ℤ.-≤- (ℕ.s≤s (n≤m +-mono n≤m₁))
ℤ.-≤- {zero} {zero} n≤m ℤ+-mono ℤ.+≤+ {zero} {zero} m≤n = ℤ.-≤- m≤n
ℤ.-≤- {m} {zero} n≤m ℤ+-mono ℤ.+≤+ {zero} {suc n} m≤n = ℤ.-≤+
ℤ.-≤-  n≤m ℤ+-mono ℤ.+≤+ {suc m} {zero} ()
ℤ.-≤- {zero} {zero} n≤m ℤ+-mono ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) =
  ℤ.+≤+ m≤n
ℤ.-≤- {zero} {suc n} () ℤ+-mono ℤ.+≤+ m≤n
ℤ.-≤- {suc m} {n} n≤m ℤ+-mono ℤ.+≤+ {zero} {zero} m≤n = ℤ.-≤- n≤m
ℤ.-≤- {suc m} {zero} z≤n ℤ+-mono ℤ.+≤+ {suc m₁} {suc n} (s≤s m≤n) =
  ℤ.-≤+ {m} {zero} ℤ+-mono ℤ.+≤+ {m₁} {n} m≤n
ℤ.-≤- {suc m} {suc n} (s≤s n≤m) ℤ+-mono ℤ.+≤+ {zero} {suc n₁} m≤n =
  ℤ.-≤+ {zero}{n₁} ℤ+-mono ℤ.-≤- n≤m
ℤ.-≤- {suc m} {suc n} (s≤s n≤m) ℤ+-mono ℤ.+≤+ {suc m₁} {suc n₁} (s≤s m≤n) =
  ℤ.-≤- n≤m ℤ+-mono ℤ.+≤+ m≤n
ℤ.+≤+ {zero} {n} m≤n ℤ+-mono ℤ.-≤+ = ℤ.-≤+
ℤ.+≤+ {suc m} {zero} () ℤ+-mono ℤ.-≤+
ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) ℤ+-mono ℤ.-≤+ {zero} {n₁} =
  ℤ.+≤+ (subst (λ a -> m ℕ.≤ suc a) (+-comm n₁ n) (≤-steps (suc n₁) (m≤n)))
ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) ℤ+-mono ℤ.-≤+ {suc m₁} {n₁} =
  ℤ.+≤+ {m} {suc n} (≤-step m≤n) ℤ+-mono ℤ.-≤+ {m₁} {n₁}
ℤ.+≤+ {zero} {zero} m≤n ℤ+-mono ℤ.-≤- n≤m = ℤ.-≤- n≤m
ℤ.+≤+ {zero} {suc n} m≤n ℤ+-mono ℤ.-≤- {n₁} {zero} n≤m = ℤ.-≤+
ℤ.+≤+ m≤n ℤ+-mono ℤ.-≤- {zero} {suc n₁} ()
ℤ.+≤+ {zero} {suc n} z≤n ℤ+-mono ℤ.-≤- {suc m} {suc n₁} (s≤s n≤m) =
  ℤ.-≤+ {zero}{n} ℤ+-mono ℤ.-≤- {m}{n₁} n≤m
ℤ.+≤+ {suc m} {zero} () ℤ+-mono ℤ.-≤- n≤m
ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) ℤ+-mono ℤ.-≤- {zero} {zero} n≤m = ℤ.+≤+ m≤n
ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) ℤ+-mono ℤ.-≤- {suc m₁} {zero} z≤n =
  ℤ.-≤+ {m₁}{zero} ℤ+-mono ℤ.+≤+ m≤n
ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) ℤ+-mono ℤ.-≤- {suc m₁} {suc n₁} (s≤s n≤m) =
  ℤ.-≤- n≤m ℤ+-mono ℤ.+≤+ m≤n
ℤ.+≤+ m≤n ℤ+-mono ℤ.+≤+ m≤n₁ = ℤ.+≤+ (m≤n +-mono m≤n₁)

_ℚ+-mono_ :  _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
_ℚ+-mono_ {p}{q}{x}{y} (*≤* pq) (*≤* xy) = *≤* (begin
  (pn ℤ.* xd ℤ.+ xn ℤ.* pd) ℤ.* (qd ℤ.* yd)
  ∼⟨ ≡⇒≤ (proj₂ ℤdistrib (qd ℤ.* yd) (pn ℤ.* xd) (xn ℤ.* pd))   ⟩
  pn ℤ.* xd ℤ.* (qd ℤ.* yd) ℤ.+ xn ℤ.* pd ℤ.* (qd ℤ.* yd) 
  ∼⟨ ≡⇒≤ (cong₂ ℤ._+_ (ℤ*-assoc pn xd (qd ℤ.* yd))
    (ℤ*-assoc xn pd (qd ℤ.* yd))) ⟩
  pn ℤ.* (xd ℤ.* (qd ℤ.* yd)) ℤ.+ xn ℤ.* (pd ℤ.* (qd ℤ.* yd)) 
  ∼⟨ ≡⇒≤ (cong₂ (λ a b -> pn ℤ.* a ℤ.+ xn ℤ.* (pd ℤ.* b)) 
    (P.sym (ℤ*-assoc xd qd yd)) (ℤ*-comm qd yd)) ⟩
  pn ℤ.* (xd ℤ.* qd ℤ.* yd) ℤ.+ xn ℤ.* (pd ℤ.* (yd ℤ.* qd)) 
  ∼⟨ ≡⇒≤ (cong₂ (λ a b -> pn ℤ.* (a ℤ.* yd) ℤ.+ xn ℤ.* b) 
    (ℤ*-comm xd qd) (P.sym (ℤ*-assoc pd yd qd))) ⟩
  pn ℤ.* (qd ℤ.* xd ℤ.* yd) ℤ.+ xn ℤ.* (pd ℤ.* yd ℤ.* qd) 
  ∼⟨ ≡⇒≤ (cong₂ (λ a b -> pn ℤ.* a ℤ.+ xn ℤ.* (b ℤ.* qd)) 
    (ℤ*-assoc qd xd yd) (ℤ*-comm pd yd)) ⟩
  pn ℤ.* (qd ℤ.* (xd ℤ.* yd)) ℤ.+ xn ℤ.* (yd ℤ.* pd ℤ.* qd) 
  ∼⟨ ≡⇒≤ (cong₂ (λ a b -> a ℤ.+ xn ℤ.* b) 
    (P.sym (ℤ*-assoc pn qd (xd ℤ.* yd))) (ℤ*-assoc yd pd qd)) ⟩
  pn ℤ.* qd ℤ.* (+ (suc xd-1 ℕ.* suc yd-1)) ℤ.+ xn ℤ.*
    (yd ℤ.* (pd ℤ.* qd))
  ∼⟨ (*-+-right-mono (yd-1 ℕ.+ xd-1 ℕ.* (suc yd-1)) pq)
    ℤ+-mono
    (≡⇒≤ (P.sym (ℤ*-assoc xn yd (pd ℤ.* qd)))) ⟩
  qn ℤ.* pd ℤ.* (xd ℤ.* yd) ℤ.+ xn ℤ.* yd ℤ.* (pd ℤ.* qd) 
  ∼⟨ (≡⇒≤ (ℤ*-assoc qn pd (xd ℤ.* yd))) ℤ+-mono
    (*-+-right-mono (qd-1 ℕ.+ pd-1 ℕ.* (suc qd-1)) xy)  ⟩
  qn ℤ.* (pd ℤ.* (xd ℤ.* yd)) ℤ.+ yn ℤ.* xd ℤ.* (pd ℤ.* qd) 
  ∼⟨ ≡⇒≤ (cong₂ (λ a b -> qn ℤ.* (pd ℤ.* a) ℤ.+ yn ℤ.* xd ℤ.* b) 
    (ℤ*-comm xd yd) (ℤ*-comm pd qd)) ⟩
  qn ℤ.* (pd ℤ.* (yd ℤ.* xd)) ℤ.+ yn ℤ.* xd ℤ.* (qd ℤ.* pd) 
  ∼⟨ ≡⇒≤ (cong₂ (λ a b -> qn ℤ.* a ℤ.+ b) 
    (P.sym (ℤ*-assoc pd yd xd )) (ℤ*-assoc yn xd (qd ℤ.* pd))) ⟩
  qn ℤ.* (pd ℤ.* yd ℤ.* xd) ℤ.+ yn ℤ.* (xd ℤ.* (qd ℤ.* pd)) 
  ∼⟨ ≡⇒≤ (cong₂ (λ a b -> qn ℤ.* (a ℤ.* xd) ℤ.+ yn ℤ.* b) 
    (ℤ*-comm pd yd) (P.sym (ℤ*-assoc xd qd pd ))) ⟩
  qn ℤ.* (yd ℤ.* pd ℤ.* xd) ℤ.+ yn ℤ.* (xd ℤ.* qd ℤ.* pd) 
  ∼⟨ ≡⇒≤ (cong₂ (λ a b -> qn ℤ.* a ℤ.+ yn ℤ.* (b ℤ.* pd)) 
    (ℤ*-assoc yd pd xd) (ℤ*-comm xd qd)) ⟩
  qn ℤ.* (yd ℤ.* (pd ℤ.* xd)) ℤ.+ yn ℤ.* (qd ℤ.* xd ℤ.* pd) 
  ∼⟨ ≡⇒≤ (cong₂ (λ a b -> a ℤ.+ yn ℤ.* b) 
    (P.sym (ℤ*-assoc qn yd (pd ℤ.* xd))) (ℤ*-assoc qd xd pd)) ⟩
  qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* (qd ℤ.* (xd ℤ.* pd)) 
  ∼⟨ ≡⇒≤ (cong (λ a -> qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* (qd ℤ.* a)) 
    (ℤ*-comm xd pd)) ⟩
  qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* (qd ℤ.* (pd ℤ.* xd)) 
  ∼⟨ ≡⇒≤ (cong (λ a -> qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ a) 
    (P.sym (ℤ*-assoc yn qd (pd ℤ.* xd)))) ⟩
  qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* qd ℤ.* (pd ℤ.* xd) 
  ∼⟨ ≡⇒≤ (P.sym (proj₂ ℤdistrib (pd ℤ.* xd) (qn ℤ.* yd) (yn ℤ.* qd))) ⟩
  (qn ℤ.* yd ℤ.+ yn ℤ.* qd) ℤ.* (pd ℤ.* xd)
        ∎)
  where
     open DecTotalOrder ℤ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
     pn = ℚ.numerator p
     pd = ℚ.denominator p
     pd-1 = ℚ.denominator-1 p
     qn = ℚ.numerator q
     qd = ℚ.denominator q
     qd-1 = ℚ.denominator-1 q
     xn = ℚ.numerator x
     xd = ℚ.denominator x
     xd-1 = ℚ.denominator-1 x
     yn = ℚ.numerator y
     yd = ℚ.denominator y
     yd-1 = ℚ.denominator-1 y

∣⊖∣-< : ∀ {m n} → m ℕ.≤ n → + ℤ.∣ m ⊖ n ∣ ≡ n ⊖ m
∣⊖∣-< {zero} {zero} (z≤n) = refl
∣⊖∣-< {zero} {suc n} (z≤n) = refl
∣⊖∣-< {suc n} (s≤s m≤n) = ∣⊖∣-< m≤n

ℤabs : {n : ℕ} -> ℤ.∣ -[1+ n ] ∣ ≡ suc n
ℤabs {zero} = refl
ℤabs {suc n} = refl

∣-∣-≤ : ∀ {m n} → m ℤ.≤ n → (+ ℤ.∣ m ℤ.- n ∣ ≡ n ℤ.- m)
∣-∣-≤ { -[1+ n ]} {+ zero} ℤ.-≤+ = refl
∣-∣-≤ { -[1+ m ]} {+ suc n} ℤ.-≤+ = trans (trans (cong (λ a -> ℤ.+
  ℤ.∣ -[1+ a ] ∣) (P.sym (+-suc m n))) (cong +_ (ℤabs {m ℕ.+ suc n})) )
    (cong +_ (P.sym (+-comm (suc n) (suc m))))
∣-∣-≤ { -[1+ m ]} { -[1+ n ] } (ℤ.-≤- n≤m) = ∣⊖∣-< n≤m
∣-∣-≤ {+ zero} {+ zero} (ℤ.+≤+ z≤s) = refl
∣-∣-≤ {+ zero} {+ suc n} (ℤ.+≤+ z≤s) = trans (cong +_ (ℤabs {n}))
  (cong +_ (P.sym (+-right-identity (suc n))))
∣-∣-≤ {+ suc m} {+ zero} (ℤ.+≤+ ())
∣-∣-≤ {+ suc m} {+ suc n} (ℤ.+≤+ m≤n) = (∣⊖∣-< {suc m}{suc n} (m≤n))


ℚ≤-abs₁ : {x y : ℚ} -> (x ≤ y) -> (∣ x - y ∣ ℚ.≃ y - x)
ℚ≤-abs₁ { -[1+ n₁ ] ÷suc d₁} { -[1+ n₂ ] ÷suc d₂} (*≤* p) = begin
    + ℤ.∣ -[1+ n₁ ] ℤ.* + (suc d₂) ℤ.- (-[1+  n₂ ] ℤ.* + (suc d₁)) ∣
    ℤ.* + ((suc d₂) ℕ.* (suc d₁)) ≡⟨ cong₂ (λ a b -> a ℤ.* + b)
    (∣-∣-≤ { -[1+ n₁ ] ℤ.* + (suc d₂)}{ (-[1+  n₂ ] ℤ.* + (suc d₁))} p)
    (*-comm (suc d₂)(suc d₁)) ⟩
  ((-[1+  n₂ ] ℤ.* + (suc d₁) ℤ.- (-[1+ n₁ ] ℤ.* + (suc d₂))) ℤ.*
  + ((suc d₁) ℕ.* (suc d₂)) ∎)
     where
     open P.≡-Reasoning
ℚ≤-abs₁ {(+ zero) ÷suc d₁} { -[1+ n₂ ] ÷suc d₂} (*≤* p) = begin
    + ℤ.∣ + zero ℤ.* + (suc d₂) ℤ.- (-[1+  n₂ ] ℤ.* + (suc d₁)) ∣
    ℤ.* + ((suc d₂) ℕ.* (suc d₁)) ≡⟨ cong₂ (λ a b -> a ℤ.* + b)
    (∣-∣-≤ { + zero ℤ.* + (suc d₂)}{ (-[1+  n₂ ] ℤ.* + (suc d₁))} p)
    (*-comm (suc d₂)(suc d₁)) ⟩
  ((-[1+  n₂ ] ℤ.* + (suc d₁) ℤ.- (+ zero ℤ.* + (suc d₂))) ℤ.*
  + ((suc d₁) ℕ.* (suc d₂)) ∎)
     where
     open P.≡-Reasoning
ℚ≤-abs₁ {(+ suc n) ÷suc d₁} { -[1+ n₂ ] ÷suc d₂} (*≤* p) = begin
    + ℤ.∣ + suc n ℤ.* + (suc d₂) ℤ.- (-[1+  n₂ ] ℤ.* + (suc d₁))
    ∣ ℤ.* + ((suc d₂) ℕ.* (suc d₁)) ≡⟨ cong₂ (λ a b -> a ℤ.* + b)
    (∣-∣-≤ { + suc n ℤ.* + (suc d₂)}{ (-[1+  n₂ ] ℤ.* + (suc d₁))} p)
    (*-comm (suc d₂)(suc d₁)) ⟩
  ((-[1+  n₂ ] ℤ.* + (suc d₁) ℤ.- (+ suc n ℤ.* + (suc d₂))) ℤ.*
  + ((suc d₁) ℕ.* (suc d₂)) ∎)
     where
     open P.≡-Reasoning
ℚ≤-abs₁ { -[1+ n ] ÷suc d₁} {(+ zero) ÷suc d₂} (*≤* p) = begin
    + ℤ.∣ -[1+ n ] ℤ.* + (suc d₂) ℤ.- (+ zero ℤ.* + (suc d₁)) ∣
    ℤ.* + ((suc d₂) ℕ.* (suc d₁)) ≡⟨ cong₂ (λ a b -> a ℤ.* + b)
    (∣-∣-≤ { -[1+ n ] ℤ.* + (suc d₂)}{ (+ zero ℤ.* + (suc d₁))} p)
    (*-comm (suc d₂)(suc d₁)) ⟩
  ((+ zero ℤ.* + (suc d₁) ℤ.- (-[1+ n ] ℤ.* + (suc d₂))) ℤ.*
  + ((suc d₁) ℕ.* (suc d₂)) ∎)
     where
     open P.≡-Reasoning
ℚ≤-abs₁ {(+ zero) ÷suc d₁} {(+ zero) ÷suc d₂} (*≤* p) = begin
    + ℤ.∣ + zero ℤ.* + (suc d₂) ℤ.- (+ zero ℤ.* + (suc d₁)) ∣ ℤ.*
    + ((suc d₂) ℕ.* (suc d₁)) ≡⟨ cong₂ (λ a b -> a ℤ.* + b)
    (∣-∣-≤ { + zero ℤ.* + (suc d₂)}{ (+ zero ℤ.* + (suc d₁))} p)
    (*-comm (suc d₂)(suc d₁)) ⟩
  ((+ zero ℤ.* + (suc d₁) ℤ.- (+ zero ℤ.* + (suc d₂))) ℤ.*
  + ((suc d₁) ℕ.* (suc d₂)) ∎)
     where
     open P.≡-Reasoning
ℚ≤-abs₁ {(+ suc n) ÷suc d₁} {(+ zero) ÷suc d₂} (*≤* p) = begin
    + ℤ.∣ + suc n ℤ.* + (suc d₂) ℤ.- (+ zero ℤ.* + (suc d₁)) ∣
    ℤ.* + ((suc d₂) ℕ.* (suc d₁)) ≡⟨ cong₂ (λ a b -> a ℤ.* + b)
    (∣-∣-≤ { + suc n ℤ.* + (suc d₂)}{ (+ zero ℤ.* + (suc d₁))} p)
    (*-comm (suc d₂)(suc d₁)) ⟩
  ((+ zero ℤ.* + (suc d₁) ℤ.- (+ suc n ℤ.* + (suc d₂))) ℤ.*
  + ((suc d₁) ℕ.* (suc d₂)) ∎)
     where
     open P.≡-Reasoning
ℚ≤-abs₁ { -[1+ n ] ÷suc d₁} {(+ suc n₁) ÷suc d₂} (*≤* p) = begin
    + ℤ.∣ -[1+ n ] ℤ.* + (suc d₂) ℤ.- (+ suc n₁ ℤ.* + (suc d₁)) ∣
    ℤ.* + ((suc d₂) ℕ.* (suc d₁)) ≡⟨ cong₂ (λ a b -> a ℤ.* + b)
    (∣-∣-≤ { -[1+ n ] ℤ.* + (suc d₂)}{ (+ suc n₁ ℤ.* + (suc d₁))} p)
    (*-comm (suc d₂)(suc d₁)) ⟩
  ((+ suc n₁ ℤ.* + (suc d₁) ℤ.- (-[1+ n ] ℤ.* + (suc d₂))) ℤ.*
  + ((suc d₁) ℕ.* (suc d₂)) ∎)
     where
     open P.≡-Reasoning
ℚ≤-abs₁ {(+ zero) ÷suc d₁} {(+ suc n₁) ÷suc d₂} (*≤* p) = begin
    + ℤ.∣ + zero ℤ.* + (suc d₂) ℤ.- (+ suc n₁ ℤ.* + (suc d₁)) ∣ ℤ.*
    + ((suc d₂) ℕ.* (suc d₁)) ≡⟨ cong₂ (λ a b -> a ℤ.* + b)
    (∣-∣-≤ { + zero ℤ.* + (suc d₂)}{ (+ suc n₁ ℤ.* + (suc d₁))} p)
    (*-comm (suc d₂)(suc d₁)) ⟩
  ((+ suc n₁ ℤ.* + (suc d₁) ℤ.- (+ zero ℤ.* + (suc d₂))) ℤ.*
  + ((suc d₁) ℕ.* (suc d₂)) ∎)
     where
     open P.≡-Reasoning
ℚ≤-abs₁ {(+ suc n) ÷suc d₁} {(+ suc n₁) ÷suc d₂} (*≤* p) = begin
    + ℤ.∣ + suc n ℤ.* + (suc d₂) ℤ.- (+ suc n₁ ℤ.* + (suc d₁)) ∣
    ℤ.* + ((suc d₂) ℕ.* (suc d₁)) ≡⟨ cong₂ (λ a b -> a ℤ.* + b)
    (∣-∣-≤ { + suc n ℤ.* + (suc d₂)}{ (+ suc n₁ ℤ.* + (suc d₁))} p)
    (*-comm (suc d₂)(suc d₁)) ⟩
  ((+ suc n₁ ℤ.* + (suc d₁) ℤ.- (+ suc n ℤ.* + (suc d₂))) ℤ.*
  + ((suc d₁) ℕ.* (suc d₂)) ∎)
     where
     open P.≡-Reasoning

⊖-≥ : ∀ {m n} → m ≥ n → m ⊖ n ≡ + (m ∸ n)
⊖-≥ z≤n       = refl
⊖-≥ (s≤s n≤m) = ⊖-≥ n≤m

ℚ≤-abs₂ : {x y : ℚ} -> (x ≤ y) -> ∣ y - x ∣ ℚ.≃ y - x
ℚ≤-abs₂ { -[1+ n ] ÷suc d} { -[1+ n₁ ] ÷suc d₁} (*≤* (ℤ.-≤- p)) = begin
  (+ ℤ.∣ suc n ℕ.* suc d₁ ℤ.⊖ suc n₁ ℕ.* suc d ∣) ℤ.* (+ suc d₁ ℤ.* + suc d)
  ≡⟨ cong (λ a -> + ℤ.∣ a ∣ ℤ.*  (+ suc d₁ ℤ.* + suc d)) ((⊖-≥ p)) ⟩
  (+ (suc n ℕ.* suc d₁ ∸ suc n₁ ℕ.* suc d )) ℤ.* (+ suc d₁ ℤ.* + suc d)
  ≡⟨ cong (λ a -> a ℤ.*  (+ suc d₁ ℤ.* + suc d)) (P.sym (⊖-≥ p)) ⟩
  (suc n ℕ.* suc d₁ ℤ.⊖ suc n₁ ℕ.* suc d) ℤ.* (+ suc d₁ ℤ.* + suc d) ∎
     where
     open P.≡-Reasoning
ℚ≤-abs₂ { -[1+ n ] ÷suc d} {(+ n₁) ÷suc d₁} le = begin
  (+ ℤ.∣ + n₁ ℤ.* + suc d ℤ.+ + suc n ℤ.* + suc d₁ ∣) ℤ.*
  (+ suc d₁ ℤ.* + suc d) ≡⟨ cong₂ (λ a b -> + ℤ.∣ a ℤ.+ b ∣ ℤ.*
  (+ suc d₁ ℤ.* + suc d)) (◃-left-inverse (+ (n₁ ℕ.* suc d)))
  (◃-left-inverse (+ suc (d₁ ℕ.+ n ℕ.* suc d₁))) ⟩
   (+ (n₁ ℕ.* suc d) ℤ.+ + (suc n ℕ.* suc d₁)) ℤ.*
   (+ suc d₁ ℤ.* + suc d) ≡⟨ cong₂ (λ a b -> (a ℤ.+ b) ℤ.*
   (+ suc d₁ ℤ.* + suc d)) (P.sym (◃-left-inverse (+ (n₁ ℕ.* suc d))))
   (P.sym (◃-left-inverse (+ (suc n ℕ.* suc d₁)))) ⟩
   (+ n₁ ℤ.* + suc d ℤ.+ + suc n ℤ.* + suc d₁) ℤ.* (+ suc d₁ ℤ.* + suc d) ∎
     where
     open P.≡-Reasoning
ℚ≤-abs₂ {(+ n) ÷suc d} { -[1+ n₁ ] ÷suc d₁}  (*≤* p) with
  subst (λ a -> a ℤ.≤ -[1+ n₁ ] ℤ.* + suc d)
  (◃-left-inverse (+ (n ℕ.* suc d₁))) p
ℚ≤-abs₂ {(+ n) ÷suc d} { -[1+ n₁ ] ÷suc d₁}  (*≤* p) | ()
ℚ≤-abs₂ {(+ zero) ÷suc d} {(+ n₁) ÷suc d₁} le = begin
  (+ ℤ.∣ + n₁ ℤ.* + suc d ℤ.+ + zero ∣) ℤ.* (+ suc d₁ ℤ.* + suc d)
  ≡⟨ cong (λ a -> + ℤ.∣ a ∣ ℤ.* (+ suc d₁ ℤ.* + suc d))
  (proj₂ ℤ+-identity (+ n₁ ℤ.* + suc d)) ⟩
   + ℤ.∣ (+ n₁ ℤ.* + suc d) ∣ ℤ.* (+ suc d₁ ℤ.* + suc d)
   ≡⟨ cong (λ a -> + ℤ.∣ a ∣ ℤ.* (+ suc d₁ ℤ.* + suc d))
   (◃-left-inverse (+ (n₁ ℕ.* suc d))) ⟩
   + (n₁ ℕ.* suc d) ℤ.* (+ suc d₁ ℤ.* + suc d)
   ≡⟨ cong (λ a -> a ℤ.* (+ suc d₁ ℤ.* + suc d))
   (P.sym (trans (proj₂ ℤ+-identity (+ n₁ ℤ.* + suc d))
   (◃-left-inverse (+ (n₁ ℕ.* suc d))))) ⟩
   (+ n₁ ℤ.* + suc d ℤ.+ + zero) ℤ.* (+ suc d₁ ℤ.* + suc d) ∎
     where
     open P.≡-Reasoning
ℚ≤-abs₂ {(+ suc n) ÷suc d} {(+ n₁) ÷suc d₁} (*≤* p) =  begin
  (+ ℤ.∣ + n₁ ℤ.* + suc d ℤ.- + suc n ℤ.* + suc d₁ ∣) ℤ.*
  (+ suc d₁ ℤ.* + suc d) ≡⟨ cong₂ (λ a b -> + ℤ.∣ a ℤ.- b ∣ ℤ.*
  (+ suc d₁ ℤ.* + suc d)) (◃-left-inverse (+ (n₁ ℕ.* suc d)))
  (◃-left-inverse (+ (suc n ℕ.* suc d₁)))   ⟩
  (+ ℤ.∣ n₁ ℕ.* suc d ℤ.⊖ suc n ℕ.* suc d₁ ∣) ℤ.*
  (+ suc d₁ ℤ.* + suc d) ≡⟨ cong (λ a -> + ℤ.∣ a ∣  ℤ.*
  (+ suc d₁ ℤ.* + suc d)) ((⊖-≥ (drop‿+≤+ (p' p)))) ⟩
  (+ (n₁ ℕ.* suc d ∸ suc n ℕ.* suc d₁ )) ℤ.* (+ suc d₁ ℤ.* + suc d)
  ≡⟨ cong (λ a -> a ℤ.*  (+ suc d₁ ℤ.* + suc d))
  (P.sym (⊖-≥ (drop‿+≤+ (p' p)))) ⟩
   (+ (n₁ ℕ.* suc d) ℤ.- + (suc n ℕ.* suc d₁)) ℤ.* (+ suc d₁ ℤ.* + suc d)
   ≡⟨ cong₂ (λ a b -> (a ℤ.- b) ℤ.*  (+ suc d₁ ℤ.* + suc d))
   (P.sym (◃-left-inverse (+ (n₁ ℕ.* suc d))))
   (P.sym (◃-left-inverse (+ (suc n ℕ.* suc d₁))))   ⟩
  (+ n₁ ℤ.* + suc d ℤ.- + suc n ℤ.* + suc d₁) ℤ.* (+ suc d₁ ℤ.* + suc d) ∎
     where
     open P.≡-Reasoning
     p' : (+ suc n ℤ.* + suc d₁ ℤ.≤ + n₁ ℤ.* + suc d) ->
       (+ (suc n ℕ.* suc d₁) ℤ.≤ + (n₁ ℕ.* suc d))
     p' p = subst₂ (λ a b -> a ℤ.≤ b)(◃-left-inverse (+ (suc n ℕ.* suc d₁)))
       ((◃-left-inverse (+ (n₁ ℕ.* suc d)))) p


⊖-< : ∀ {m n} → m < n -> m ⊖ n ≡ ℤ.- ℤ.+ (n ∸ m)
⊖-< {zero}  (s≤s z≤n) = refl
⊖-< {suc m} (s≤s m<n) = ⊖-< m<n

x-x : {x : ℚ} -> (x - x ℚ.≃ (+ 0) ÷suc 0)
x-x {(+ zero) ÷suc d} = refl
x-x {(+ suc n) ÷suc d} = begin (+ suc n ℤ.* + suc d ℤ.-
  + suc n ℤ.* + suc d) ℤ.* + 1
    ≡⟨ cong (λ a -> a ℤ.* + 1) (n⊖n≡0 (suc n ℕ.* suc d))  ⟩
    + 0 ∎
    where
      open P.≡-Reasoning
x-x { -[1+ n ] ÷suc d} = begin (-[1+ n ] ℤ.* + suc d ℤ.-
  -[1+ n ] ℤ.* + suc d) ℤ.* + 1
    ≡⟨ cong (λ a -> a ℤ.* + 1) (n⊖n≡0 (suc n ℕ.* suc d))  ⟩
    + 0 ∎
    where
      open P.≡-Reasoning

left-identity : {x : ℚ} -> x ℚ.≃ (+ 0) ÷suc 0 + x
left-identity {n ÷suc d} = begin
  n ℤ.* + suc (d ℕ.+ zero) ≡⟨ cong₂ (λ a b -> a ℤ.* + b)
    (P.sym (proj₂ ℤ*-identity n)) (+-right-identity (suc d))  ⟩
  n ℤ.* (+ 1) ℤ.* + suc d ≡⟨ cong (λ a -> a ℤ.* + suc d) {n ℤ.* (+ 1)}
    {+ 0 ℤ.+ n ℤ.* (+ 1)} (P.sym (proj₁ ℤ+-identity (n ℤ.* (+ suc zero))))⟩
  (+ 0 ℤ.+ n ℤ.* (+ 1)) ℤ.* + suc d ≡⟨ cong (λ a -> (a ℤ.+ n ℤ.* (+ 1))
    ℤ.* + suc d) {+ 0}{+ 0 ℤ.* + suc d}
      (P.sym (◃-left-inverse (+ (0 ℕ.* suc d))))   ⟩
  (+ 0 ℤ.* + suc d ℤ.+ n ℤ.* (+ 1)) ℤ.* + suc d ∎ 
    where
      open P.≡-Reasoning

right-identity : {x : ℚ} -> x ℚ.≃ x + (+ 0) ÷suc 0
right-identity {n ÷suc d} = begin n ℤ.* (+ suc d ℤ.* + 1)
  ≡⟨ cong (λ a -> n ℤ.* a) ((ℤ*-comm (+ suc d)(+ 1)))  ⟩
    n ℤ.* (+ 1 ℤ.* + suc d) ≡⟨ P.sym (ℤ*-assoc n (+ 1) (+ suc d)) ⟩
    n ℤ.* (+ 1) ℤ.* + suc d ≡⟨ cong (λ a -> a ℤ.* + suc d)
      (P.sym (proj₂ ℤ+-identity (n ℤ.* (+ 1)))) ⟩
    (n ℤ.* (+ 1) ℤ.+ + 0 ℤ.* + suc d) ℤ.* + suc d ∎ 
    where
      open P.≡-Reasoning

ℚ+-comm : (x y :  ℚ) -> x + y ℚ.≃ y + x
ℚ+-comm (n₁ ÷suc d₁)(n₂ ÷suc d₂) = cong₂ ℤ._*_ (ℤ+-comm (n₁ ℤ.* + suc d₂)
  (n₂ ℤ.* + suc d₁)) (ℤ*-comm (+ suc d₂)(+ suc d₁))

ℚ+-assoc : (x y z : ℚ) -> x + y + z ℚ.≃ x + (y + z)
ℚ+-assoc (n₁ ÷suc d₁)  (n₂ ÷suc d₂) (n₃ ÷suc d₃) = begin
  ((n₁ ℤ.* D₂ ℤ.+ n₂ ℤ.* D₁) ℤ.* D₃ ℤ.+ n₃ ℤ.* (D₁ ℤ.* D₂))
  ℤ.* (D₁ ℤ.* (D₂ ℤ.* D₃)) ≡⟨ cong (λ a -> ((n₁ ℤ.* D₂ ℤ.+ n₂ ℤ.* D₁) ℤ.* D₃
  ℤ.+ n₃ ℤ.* (D₁ ℤ.* D₂))ℤ.* a) (P.sym (ℤ*-assoc (D₁)(D₂)(D₃))) ⟩
  ((n₁ ℤ.* D₂ ℤ.+ n₂ ℤ.* D₁) ℤ.* D₃ ℤ.+ n₃ ℤ.* (D₁ ℤ.* D₂)) ℤ.* den
  ≡⟨ cong (λ a -> (a ℤ.+  n₃ ℤ.* (D₁ ℤ.* D₂)) ℤ.* den)
  (proj₂ ℤdistrib D₃ (n₁ ℤ.* D₂) (n₂ ℤ.* D₁))⟩
  (n₁ ℤ.* D₂ ℤ.* D₃ ℤ.+ n₂ ℤ.* D₁ ℤ.* D₃ ℤ.+ n₃ ℤ.* (D₁ ℤ.* D₂)) ℤ.* den
  ≡⟨ cong (λ a -> a ℤ.* den) (ℤ+-assoc (n₁ ℤ.* D₂ ℤ.* D₃)
    (n₂ ℤ.* D₁ ℤ.* D₃) (n₃ ℤ.* (D₁ ℤ.* D₂)))⟩
  (n₁ ℤ.* D₂ ℤ.* D₃ ℤ.+ (n₂ ℤ.* D₁ ℤ.* D₃ ℤ.+ n₃ ℤ.* (D₁ ℤ.* D₂))) ℤ.* den
  ≡⟨ cong₂ (λ a b -> (a ℤ.+ (n₂ ℤ.* D₁ ℤ.* D₃ ℤ.+ n₃ ℤ.* b)) ℤ.* den)
    (ℤ*-assoc n₁ D₂ D₃) (ℤ*-comm D₁ D₂) ⟩
  (n₁ ℤ.* (D₂ ℤ.* D₃) ℤ.+ (n₂ ℤ.* D₁ ℤ.* D₃ ℤ.+ n₃ ℤ.* (D₂ ℤ.* D₁))) ℤ.* den
  ≡⟨ cong₂ (λ a b -> (n₁ ℤ.* (D₂ ℤ.* D₃) ℤ.+ (a ℤ.+ b)) ℤ.* den)
    (ℤ*-assoc n₂ D₁ D₃) (P.sym (ℤ*-assoc n₃ D₂ D₁))⟩
 (n₁ ℤ.* (D₂ ℤ.* D₃) ℤ.+ (n₂ ℤ.* (D₁ ℤ.* D₃) ℤ.+ n₃ ℤ.* D₂ ℤ.* D₁)) ℤ.* den
 ≡⟨ cong (λ a -> (n₁ ℤ.* (D₂ ℤ.* D₃) ℤ.+ (n₂ ℤ.* a ℤ.+ n₃ ℤ.* D₂ ℤ.* D₁))
 ℤ.* den) (ℤ*-comm D₁ D₃)  ⟩
  (n₁ ℤ.* (D₂ ℤ.* D₃) ℤ.+ (n₂ ℤ.* (D₃ ℤ.* D₁) ℤ.+ n₃ ℤ.* D₂ ℤ.* D₁)) ℤ.*
  den ≡⟨ cong (λ a -> (n₁ ℤ.* (D₂ ℤ.* D₃) ℤ.+ (a ℤ.+ n₃ ℤ.* D₂ ℤ.* D₁))
    ℤ.* den) (P.sym (ℤ*-assoc n₂ D₃ D₁))  ⟩
  (n₁ ℤ.* (D₂ ℤ.* D₃) ℤ.+ (n₂ ℤ.* D₃ ℤ.* D₁ ℤ.+ n₃ ℤ.* D₂ ℤ.* D₁)) ℤ.* den
  ≡⟨ cong (λ a -> (n₁ ℤ.* (D₂ ℤ.* D₃) ℤ.+ a) ℤ.* den)
    (P.sym (proj₂ ℤdistrib D₁ (n₂ ℤ.* D₃) (n₃ ℤ.* D₂)))⟩
  (n₁ ℤ.* (D₂ ℤ.* D₃) ℤ.+ (n₂ ℤ.* D₃ ℤ.+ n₃ ℤ.* D₂) ℤ.* D₁) ℤ.* den ∎
    where
     open P.≡-Reasoning
     den = (+ suc d₁ ℤ.* + suc d₂ ℤ.* + suc d₃)
     D₁ = + suc d₁
     D₂ = + suc d₂
     D₃ = + suc d₃

_ℤ<_ : Rel ℤ Level.zero
m ℤ< n = ℤ.suc m ℤ.≤ n

_ℤ>_ : Rel ℤ Level.zero
m ℤ> n = n ℤ< m

_ℤ≰_ : Rel ℤ Level.zero
a ℤ≰ b = ¬ a ℤ.≤ b

ℤ≤⇒pred≤ : ∀ m n → ℤ.suc m ℤ.≤ n → m ℤ.≤ n
ℤ≤⇒pred≤ -[1+ zero ] -[1+ n₁ ] ()
ℤ≤⇒pred≤ -[1+ suc n ] -[1+ n₁ ] (ℤ.-≤- le) = ℤ.-≤- (≤-step le)
ℤ≤⇒pred≤ -[1+ zero ] (+ n₁) le = ℤ.-≤+
ℤ≤⇒pred≤ -[1+ suc n ] (+ n₁) le = ℤ.-≤+
ℤ≤⇒pred≤ (+ n) -[1+ n₁ ] ()
ℤ≤⇒pred≤ (+ zero) (+ n₁) le = ℤ.+≤+ z≤n
ℤ≤⇒pred≤ (+ suc n) (+ n₁) (ℤ.+≤+ le) = ℤ.+≤+ (≤⇒pred≤ (suc (suc n)) n₁ le)

ℤ≰⇒> : (_ℤ≰_) ⇒ _ℤ>_
ℤ≰⇒> { -[1+ n ]} { -[1+ zero ]} p = ⊥-elim (p (ℤ.-≤- z≤n))
ℤ≰⇒> { -[1+ zero ]} { -[1+ suc n₁ ]} p = ℤ.-≤- z≤n
ℤ≰⇒> { -[1+ suc n ]} { -[1+ suc n₁ ]} p = ℤ.-≤- (≰⇒> {n₁} {n}
  (p ∘ (λ x → ℤ.-≤- (s≤s x))))
ℤ≰⇒> { -[1+ n ]} {+ n₁} p = ⊥-elim (p (ℤ.-≤+))
ℤ≰⇒> {+ n} { -[1+ zero ]} p = ℤ.+≤+ z≤n
ℤ≰⇒> {+ n} { -[1+ suc n₁ ]} p = ℤ.-≤+
ℤ≰⇒> {+ zero} {+ n} p = ⊥-elim (p (ℤ.+≤+ z≤n))
ℤ≰⇒> {+ suc n} {+ zero} p = ℤ.+≤+ (s≤s z≤n)
ℤ≰⇒> {+ suc n} {+ suc n₁} p = ℤ.+≤+ (s≤s (≰⇒> {n} {n₁}
  (p ∘ (λ x → ℤ.+≤+ (s≤s x)))))

data _ℚ<_ : ℚ → ℚ → Set where
  *≤* : ∀ {p q} →
        (ℚ.numerator p ℤ.* (+ suc (ℚ.denominator-1 q))) ℤ<
        (ℚ.numerator q ℤ.* (+ suc (ℚ.denominator-1 p))) →
        p ℚ< q

_ℚ>_ : Rel ℚ Level.zero
m ℚ> n = n ℚ< m

_ℚ≰_ : Rel ℚ Level.zero
a ℚ≰ b = ¬ a ℚ.≤ b

ℚ≰⇒> : _ℚ≰_ ⇒ _ℚ>_
ℚ≰⇒> ¬p = *≤* (ℤ≰⇒> (λ z → ¬p (*≤* z)))

<⇒≤ : _ℚ<_ ⇒ _≤_
<⇒≤ (*≤* le) = *≤* (ℤ≤⇒pred≤ _ _ le)

triang : (x y z : ℚ) -> (∣ x - z ∣ ≤ ∣ x - y ∣ + ∣ y - z ∣)
triang x y z with x ℚ.≤? y | y ℚ.≤? z | x ℚ.≤? z
triang x y z | yes p | yes p₁ | yes p₂ = begin
  ∣ x - z ∣   ∼⟨ ≡⇒≤ (ℚ≤-abs₁ p₂)   ⟩
  z - x ∼⟨ ≡⇒≤ (right-identity {z - x}) ⟩
  (z - x) + ((+ 0) ÷suc 0) ∼⟨  ≡⇒≤ {(z - x)}{(z - x)} refl
  ℚ+-mono ≡⇒≤ {(+ 0) ÷suc 0}{(y - y)}
  (ℚsym {y - y}{(+ 0) ÷suc 0} (x-x {y})) ⟩
  (z - x) + (y - y) ∼⟨ ≡⇒≤ {z - x}{ - x + z} (ℚ+-comm z (- x))
  ℚ+-mono (≡⇒≤ {(y - y)}{(y - y)} refl)   ⟩
  - x + z + (y - y) ∼⟨ ≡⇒≤ (ℚ+-assoc (- x) z (y - y) )   ⟩
  - x + (z + (y - y)) ∼⟨ ≡⇒≤ { - x}{ - x} refl
  ℚ+-mono ≡⇒≤ {z + (y - y)}{z + y - y}
  (ℚsym {z + y - y}{z + (y - y)} (ℚ+-assoc z y (- y)) )   ⟩
  - x + (z + y - y) ∼⟨ ≡⇒≤ { - x}{ - x} refl ℚ+-mono
  (≡⇒≤ {z + y}{y + z} (ℚ+-comm z y )
  ℚ+-mono ≡⇒≤ { - y}{ - y} refl)   ⟩
  - x + (y + z - y) ∼⟨ ≡⇒≤ { - x}{ - x} refl
  ℚ+-mono ≡⇒≤ {y + z - y}{y + (z - y)} (ℚ+-assoc y z (- y) )   ⟩
  - x + (y + (z - y)) ∼⟨ ≡⇒≤ { - x + (y + (z - y))}{ - x + y + (z - y)}
  (ℚsym { - x + y + (z - y)}{ - x + (y + (z - y))}
  (ℚ+-assoc (- x) y (z - y) ))   ⟩
  - x + y + (z - y) ∼⟨ ≡⇒≤ { - x + y}{y - x}
  (ℚ+-comm (- x) y) ℚ+-mono ≡⇒≤ {z - y}{z - y} refl  ⟩
  (y - x) + (z - y) ∼⟨  ≡⇒≤ {y - x}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{y - x}
  (ℚ≤-abs₁ {x}{y} p)) ℚ+-mono ≡⇒≤ {z - y}{∣ y - z ∣}
  (ℚsym {∣ y - z ∣}{z - y} (ℚ≤-abs₁ {y}{z} p₁))   ⟩
  ∣ x - y ∣ + ∣ y - z ∣ ∎
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
triang x y z | yes p | yes p₁ | no ¬p = ⊥-elim (¬p (≤trans p p₁))
  where
  open DecTotalOrder ℚ.decTotalOrder using ()
      renaming (trans to ≤trans)
triang x y z | yes p | no ¬p | yes p₁ = begin 
  ∣ x - z ∣   ∼⟨ ≡⇒≤ (ℚ≤-abs₁ p₁)   ⟩
  z - x ∼⟨ ≡⇒≤ (right-identity {z - x}) ⟩
  (z - x) + ((+ 0) ÷suc 0) ∼⟨  ≡⇒≤ {(z - x)}{(z - x)} refl ℚ+-mono
  ≡⇒≤ {(+ 0) ÷suc 0}{(z - z)}(ℚsym {z - z}{(+ 0) ÷suc 0} (x-x {z})) ⟩
  z - x + (z - z) ∼⟨ ((<⇒≤ (ℚ≰⇒> ¬p)) ℚ+-mono ≡⇒≤ { - x}{ - x} refl)
  ℚ+-mono ((<⇒≤ (ℚ≰⇒> ¬p)) ℚ+-mono ≡⇒≤ { - z}{ - z} refl) ⟩
  (y - x) + (y - z) ∼⟨  ≡⇒≤ {y - x}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{y - x}
  (ℚ≤-abs₁ {x}{y} p)) ℚ+-mono ≡⇒≤ {y - z}{∣ y - z ∣}
  (ℚsym {∣ y - z ∣}{y - z} (ℚ≤-abs₂ (<⇒≤ (ℚ≰⇒> ¬p))))⟩
  ∣ x - y ∣ + ∣ y - z ∣ ∎ 
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
triang x y z | yes p | no ¬p | no ¬p₁ = begin
  ∣ x - z ∣   ∼⟨ ≡⇒≤ (ℚ≤-abs₂ (<⇒≤ (ℚ≰⇒> ¬p₁))) ⟩
  (x - z) ∼⟨   ≡⇒≤ (left-identity {x - z})  ⟩
  (+ 0) ÷suc 0 + (x - z) ∼⟨  ≡⇒≤ {(+ 0) ÷suc 0}{x - x}
  (ℚsym {x - x}{(+ 0) ÷suc 0} (x-x {x})) ℚ+-mono ≡⇒≤ {x - z}{x - z} refl ⟩
  (x - x) + (x - z) ∼⟨  (p  ℚ+-mono ≡⇒≤ { - x}{ - x} refl ) ℚ+-mono
  (p ℚ+-mono ≡⇒≤ { - z}{ - z} refl) ⟩
  (y - x) + (y - z) ∼⟨  ≡⇒≤ {y - x}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{y - x}
  (ℚ≤-abs₁ p)) ℚ+-mono ≡⇒≤ {y - z}{∣ y - z ∣} (ℚsym {∣ y - z ∣}{y - z}
  (ℚ≤-abs₂ (<⇒≤ (ℚ≰⇒> ¬p))))⟩ 
  ∣ x - y ∣ + ∣ y - z ∣ ∎ 
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
triang x y z | no ¬p | yes p | yes p₁ = begin
  ∣ x - z ∣                 ∼⟨ ≡⇒≤ (ℚ≤-abs₁ p₁)   ⟩
  z - x                    ∼⟨ ≡⇒≤ (right-identity {z - x}) ⟩
  (z - x) + ((+ 0) ÷suc 0) ∼⟨  ≡⇒≤ {(z - x)}{(z - x)} refl
  ℚ+-mono ≡⇒≤ {(+ 0) ÷suc 0}{(y - y)}(ℚsym {y - y}{(+ 0)÷suc 0}(x-x {y}))⟩
  z - x + (y - y)          ∼⟨ ≡⇒≤ (ℚ+-assoc z (- x) (y - y)) ⟩
  z + (- x + (y - y))      ∼⟨ ≡⇒≤ {z}{z} refl ℚ+-mono
  ≡⇒≤ { - x + (y - y)}{ - x + y - y}
  (ℚsym { - x + y - y}{ - x + (y - y)} (ℚ+-assoc (- x) y (- y))) ⟩
  z + (- x + y - y)        ∼⟨ ≡⇒≤ {z}{z} refl ℚ+-mono
  ((≡⇒≤ { - x}{ - x} refl  ℚ+-mono  (<⇒≤ (ℚ≰⇒> ¬p)))
  ℚ+-mono (≡⇒≤ { - y}{ - y} refl)) ⟩
  z + (- x + x - y)        ∼⟨ ≡⇒≤ {z}{z} refl ℚ+-mono
  (≡⇒≤ { - x + x}{(+ 0)÷suc 0} (ℚtrans { - x + x}{x - x}{(+ 0)÷suc 0}
  (ℚ+-comm (- x) x) (x-x {x})) ℚ+-mono ≡⇒≤ { - y}{ - y} refl) ⟩
  z + ((+ 0)÷suc 0 - y) ∼⟨ ≡⇒≤ {z}{z} refl ℚ+-mono
  ≡⇒≤ {((+ 0)÷suc 0 - y)}{ - y} (ℚsym { - y}{((+ 0)÷suc 0 - y)}
  (left-identity { - y})) ⟩
  z - y ∼⟨ ≡⇒≤  (left-identity {z - y}) ⟩
  ((+ 0) ÷suc 0) + (z - y) ∼⟨ ≡⇒≤ {(+ 0) ÷suc 0}{(y - y)}
  (ℚsym {y - y}{(+ 0) ÷suc 0}(x-x {y})) ℚ+-mono ≡⇒≤ {z - y}{z - y} refl ⟩
  y - y + (z - y) ∼⟨ (<⇒≤ (ℚ≰⇒> ¬p) ℚ+-mono ≡⇒≤ { - y}{ - y} refl)
  ℚ+-mono ≡⇒≤ {z - y}{z - y} refl ⟩
  x - y + (z - y) ∼⟨ ≡⇒≤ {x - y}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{x - y}
  (ℚ≤-abs₂ (<⇒≤ (ℚ≰⇒> ¬p)))) ℚ+-mono ≡⇒≤ {z - y}{∣ y - z ∣}
  (ℚsym {∣ y - z ∣}{z - y} (ℚ≤-abs₁ p)) ⟩
  ∣ x - y ∣ + ∣ y - z ∣ ∎ 
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
triang x y z | no ¬p | yes p | no ¬p₁ = begin
  ∣ x - z ∣   ∼⟨ ≡⇒≤ (ℚ≤-abs₂ (<⇒≤ (ℚ≰⇒> ¬p₁)))   ⟩
  x - z ∼⟨ ≡⇒≤ (right-identity {x - z}) ⟩
  (x - z) + ((+ 0) ÷suc 0) ∼⟨  ≡⇒≤ {x - z}{x - z} refl
  ℚ+-mono ≡⇒≤ {(+ 0) ÷suc 0}{(y - y)}(ℚsym {y - y}{(+ 0)÷suc 0}(x-x {y}))⟩
  x - z + (y - y) ∼⟨ ≡⇒≤ (ℚ+-assoc x (- z) (y - y)) ⟩
  x + (- z + (y - y)) ∼⟨ ≡⇒≤ {x}{x} refl ℚ+-mono
  ≡⇒≤ { - z + (y - y)}{ - z + y - y}
  (ℚsym { - z + y - y}{ - z + (y - y)} (ℚ+-assoc (- z) y (- y))) ⟩
  x + (- z + y - y) ∼⟨ ≡⇒≤ {x}{x} refl ℚ+-mono ((≡⇒≤ { - z}{ - z} refl
  ℚ+-mono p)  ℚ+-mono (≡⇒≤ { - y}{ - y} refl)) ⟩
  x + (- z + z - y) ∼⟨ ≡⇒≤ {x}{x} refl ℚ+-mono
  (≡⇒≤ { - z + z}{(+ 0)÷suc 0} (ℚtrans { - z + z}{z - z}{(+ 0)÷suc 0}
  (ℚ+-comm (- z) z) (x-x {z})) ℚ+-mono ≡⇒≤ { - y}{ - y} refl) ⟩
  x + ((+ 0) ÷suc 0 - y) ∼⟨ ≡⇒≤ {x}{x} refl ℚ+-mono
  ≡⇒≤ {(+ 0)÷suc 0 - y}{ - y}(ℚsym { - y}{(+ 0)÷suc 0 - y}
    (left-identity { - y}))⟩
  x - y ∼⟨ ≡⇒≤ (right-identity {x - y})  ⟩
  x - y + (+ 0) ÷suc 0 ∼⟨ ≡⇒≤ {x - y}{x - y} refl ℚ+-mono
  ≡⇒≤ {(+ 0) ÷suc 0}{y - y}(ℚsym {y - y}{(+ 0) ÷suc 0} (x-x {y})) ⟩
  x - y + (y - y) ∼⟨ ≡⇒≤ {x - y}{x - y} refl ℚ+-mono
  (p ℚ+-mono ≡⇒≤ { - y}{ - y} refl) ⟩
  x - y + (z - y) ∼⟨ ≡⇒≤ {x - y}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{x - y}
  (ℚ≤-abs₂ (<⇒≤ (ℚ≰⇒> ¬p)))) ℚ+-mono ≡⇒≤ {z - y}{∣ y - z ∣}
  (ℚsym {∣ y - z ∣}{z - y} (ℚ≤-abs₁ p)) ⟩
  ∣ x - y ∣ + ∣ y - z ∣ ∎
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
triang x y z | no ¬p | no ¬p₁ | yes p =
  ⊥-elim (¬p (≤trans p (<⇒≤ (ℚ≰⇒> ¬p₁))))
  where
  open DecTotalOrder ℚ.decTotalOrder using ()
      renaming (trans to ≤trans)
triang x y z | no ¬p | no ¬p₁ | no ¬p₂ = begin 
  ∣ x - z ∣             ∼⟨ ≡⇒≤ (ℚ≤-abs₂ (<⇒≤ (ℚ≰⇒> ¬p₂)))   ⟩
  x - z                ∼⟨ ≡⇒≤ {x}{x + (+ 0)÷suc 0}
  (right-identity {x}) ℚ+-mono ≡⇒≤ { - z}{ - z} refl ⟩
  x + (+ 0) ÷suc 0 - z ∼⟨ (≡⇒≤ {x}{x} refl  ℚ+-mono
  ≡⇒≤ {(+ 0)÷suc 0}{y - y} (ℚsym {y - y}{(+ 0)÷suc 0} (x-x {y}))) ℚ+-mono
  ≡⇒≤ { - z}{ - z} refl ⟩
  x + (y - y) - z      ∼⟨ (≡⇒≤ {x}{x} refl  ℚ+-mono
  ≡⇒≤ {y - y}{ - y + y} (ℚ+-comm y (- y))) ℚ+-mono ≡⇒≤ { - z}{ - z}refl ⟩
  x + (- y + y) - z    ∼⟨ ≡⇒≤ {x + (- y + y)}{x - y + y}
  (ℚsym {x - y + y}{x + (- y + y)}(ℚ+-assoc x (- y) y)) ℚ+-mono
    ≡⇒≤ { - z}{ - z} refl ⟩
  x - y + y - z        ∼⟨ ≡⇒≤ { x - y + y - z}{x - y + (y - z)}
    (ℚ+-assoc (x - y) y (- z)) ⟩
  x - y + (y - z)      ∼⟨ ≡⇒≤ {x - y}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{x - y}
    (ℚ≤-abs₂ (<⇒≤ (ℚ≰⇒> ¬p)))) ℚ+-mono
    ≡⇒≤ {y - z}{∣ y - z ∣}(ℚsym {∣ y - z ∣}{y - z}(ℚ≤-abs₂ (<⇒≤ (ℚ≰⇒> ¬p₁))))⟩  
  ∣ x - y ∣ + ∣ y - z ∣ ∎
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder

