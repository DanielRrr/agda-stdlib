module Data.Rational.Properties where

open import Data.Sum
open import Relation.Nullary.Core using (yes; no)
open import Relation.Nullary.Decidable
open import Data.Rational as ℚ using (ℚ; -_ ; _*_; _÷suc_; _-_; _+_; ∣_∣; 
  decTotalOrder; _≤_; *≤* ; _≤?_; _÷_; _≃_)
open import Data.Integer as ℤ using (decTotalOrder; ℤ; +_ ; -[1+_]; drop‿-≤-; _≤?_; _⊖_) renaming 
  (_-_ to ℤ_-_; _+_ to _ℤ+_; _*_ to  _ℤ*_;_≤_ to ℤ_≤_)
open import Data.Nat as ℕ using (ℕ; suc; zero; pred; compare; _<_; _∸_; s≤s; z≤n) renaming (_≤_ to ℕ_≤_; _≤?_ to _≤??_)
open import Data.Nat.Properties.Simple using (+-comm; +-suc;
  *-comm; +-right-identity)
open import Relation.Binary.Core using (_Preserves₂_⟶_⟶_; IsEquivalence)
open import Data.Nat.Properties using (m≤m+n; _+-mono_; ≤-steps; ≤-step)
import Relation.Binary.PreorderReasoning as Pre
open import Relation.Binary.PropositionalEquality.Core using (trans; subst)
open import Algebra using (module CommutativeRing)
open import Data.Integer.Properties using (commutativeRing; abs-◃; *-+-right-mono; cancel-*-+-right-≤)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; 
  subst; cong; cong₂; subst₂)
open import Data.Product
open import Relation.Binary using (module DecTotalOrder)
open CommutativeRing commutativeRing
  using ()
  renaming (distrib to ℤdistrib; +-assoc to ℤ+-assoc; *-assoc to ℤ*-assoc; 
    *-comm to ℤ*-comm; +-comm to ℤ+-comm; *-identity to ℤ*-identity)


--This module contains various lemmas and additional functions rational numbers
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


--Since the we have defined rationals without requireming coprimality, 
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

postulate ℚtriang : (x y z : ℚ) -> (∣ x - z ∣ ≤ ∣ x - y ∣ + ∣ y - z ∣)

⊖-< : ∀ {m n} → m < n → m ⊖ n ≡ ℤ.- ℤ.+ (n ∸ m)
⊖-< {zero}  (s≤s z≤n) = refl
⊖-< {suc m} (s≤s m<n) = ⊖-< m<n

⊖-≥ : ∀ {m n} → n ℕ.≤ m → m ⊖ n ≡ + (m ∸ n)
⊖-≥ z≤n       = refl
⊖-≥ (s≤s n≤m) = ⊖-≥ n≤m

_ℤ+-mono_ :  ℤ._+_ Preserves₂ ℤ._≤_ ⟶ ℤ._≤_ ⟶ ℤ._≤_
ℤ.-≤+ ℤ+-mono ℤ.-≤+ = ℤ.-≤+
ℤ.-≤+ {n} {zero} ℤ+-mono ℤ.-≤- {m} {zero} m₁≤n₁ = ℤ.-≤- z≤n
ℤ.-≤+ ℤ+-mono ℤ.-≤- {zero} {suc n} ()
ℤ.-≤+ {zero} {zero} ℤ+-mono ℤ.-≤- {suc m} {suc n} m₁≤n₁ = ℤ.-≤- (z≤n {suc zero} +-mono m₁≤n₁)
ℤ.-≤+ {m} {suc n} ℤ+-mono ℤ.-≤- {m₁} {zero} m₁≤n₁ = ℤ.-≤+
ℤ.-≤+ {zero} {suc n} ℤ+-mono ℤ.-≤- {suc m} {suc n₁} (s≤s m₁≤n₁) = ℤ.-≤+ {suc zero} {n} ℤ+-mono ℤ.-≤- {m} {n₁} (m₁≤n₁)
ℤ.-≤+ {suc m} {zero} ℤ+-mono ℤ.-≤- {suc m₁} {suc n} m₁≤n₁ = ℤ.-≤- (≤-steps (suc (suc m)) m₁≤n₁)
ℤ.-≤+ {suc m} {suc n} ℤ+-mono ℤ.-≤- {suc m₁} {suc n₁} (s≤s m₁≤n₁) = ℤ.-≤+ {suc m} {n} ℤ+-mono ℤ.-≤- {suc m₁} {n₁} (≤-step m₁≤n₁)
ℤ.-≤+ ℤ+-mono ℤ.+≤+ {zero} {n₁} m≤n = ℤ.-≤+
ℤ.-≤+ ℤ+-mono ℤ.+≤+ {suc m₁} {zero} () 
ℤ.-≤+ {zero} {n} ℤ+-mono ℤ.+≤+ {suc m₁} {suc n₁} (s≤s m≤n) = ℤ.+≤+ (≤-steps n (≤-step m≤n))
ℤ.-≤+ {suc m} {n} ℤ+-mono ℤ.+≤+ {suc m₁} {suc n₁} (s≤s m≤n) = ℤ.-≤+ {m}{n} ℤ+-mono ℤ.+≤+ {m₁}{suc n₁} (≤-step m≤n)
ℤ.-≤- {m} {zero} n≤m ℤ+-mono ℤ.-≤+ {n₁} {zero} = ℤ.-≤- z≤n
ℤ.-≤- {m} {zero} n≤m ℤ+-mono ℤ.-≤+ {n₁} {suc n} = ℤ.-≤+
ℤ.-≤- {zero} {suc n}() ℤ+-mono ℤ.-≤+
ℤ.-≤- {suc m} {suc n} n≤m ℤ+-mono ℤ.-≤+ {zero} {zero} = ℤ.-≤- (subst₂ (λ a b -> a ℕ.≤ suc b) (+-right-identity (suc n)) (+-suc m zero) (n≤m +-mono z≤n {suc zero}))
ℤ.-≤- {suc m} {suc n} (s≤s n≤m) ℤ+-mono ℤ.-≤+ {m₁} {suc n₁} = ℤ.-≤- {suc m} {n} (≤-step n≤m) ℤ+-mono ℤ.-≤+ {m₁}{n₁}
ℤ.-≤- {suc m} {suc n} (s≤s n≤m) ℤ+-mono ℤ.-≤+ {m₁} {zero} = ℤ.-≤- (subst (λ a -> suc n ℕ.≤ suc (suc a)) (+-comm m₁ m) (s≤s (≤-step (≤-steps m₁ n≤m))))
ℤ.-≤- {m} {n}  n≤m ℤ+-mono ℤ.-≤-  n≤m₁ = ℤ.-≤- (ℕ.s≤s (n≤m +-mono n≤m₁))
ℤ.-≤- {zero} {zero} n≤m ℤ+-mono ℤ.+≤+ {zero} {zero} m≤n = ℤ.-≤- m≤n
ℤ.-≤- {m} {zero} n≤m ℤ+-mono ℤ.+≤+ {zero} {suc n} m≤n = ℤ.-≤+
ℤ.-≤-  n≤m ℤ+-mono ℤ.+≤+ {suc m} {zero} ()
ℤ.-≤- {zero} {zero} n≤m ℤ+-mono ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) = ℤ.+≤+ m≤n
ℤ.-≤- {zero} {suc n} () ℤ+-mono ℤ.+≤+ m≤n
ℤ.-≤- {suc m} {n} n≤m ℤ+-mono ℤ.+≤+ {zero} {zero} m≤n = ℤ.-≤- n≤m
ℤ.-≤- {suc m} {zero} z≤n ℤ+-mono ℤ.+≤+ {suc m₁} {suc n} (s≤s m≤n) = ℤ.-≤+ {m} {zero} ℤ+-mono ℤ.+≤+ {m₁} {n} m≤n
ℤ.-≤- {suc m} {suc n} (s≤s n≤m) ℤ+-mono ℤ.+≤+ {zero} {suc n₁} m≤n = ℤ.-≤+ {zero}{n₁} ℤ+-mono ℤ.-≤- n≤m
ℤ.-≤- {suc m} {suc n} (s≤s n≤m) ℤ+-mono ℤ.+≤+ {suc m₁} {suc n₁} (s≤s m≤n) = ℤ.-≤- n≤m ℤ+-mono ℤ.+≤+ m≤n
ℤ.+≤+ {zero} {n} m≤n ℤ+-mono ℤ.-≤+ = ℤ.-≤+
ℤ.+≤+ {suc m} {zero} () ℤ+-mono ℤ.-≤+
ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) ℤ+-mono ℤ.-≤+ {zero} {n₁} = ℤ.+≤+ (subst (λ a -> m ℕ.≤ suc a) (+-comm n₁ n) (≤-steps (suc n₁) (m≤n)))
ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) ℤ+-mono ℤ.-≤+ {suc m₁} {n₁} = ℤ.+≤+ {m} {suc n} (≤-step m≤n) ℤ+-mono ℤ.-≤+ {m₁} {n₁}
ℤ.+≤+ {zero} {zero} m≤n ℤ+-mono ℤ.-≤- n≤m = ℤ.-≤- n≤m
ℤ.+≤+ {zero} {suc n} m≤n ℤ+-mono ℤ.-≤- {n₁} {zero} n≤m = ℤ.-≤+
ℤ.+≤+ m≤n ℤ+-mono ℤ.-≤- {zero} {suc n₁} ()
ℤ.+≤+ {zero} {suc n} z≤n ℤ+-mono ℤ.-≤- {suc m} {suc n₁} (s≤s n≤m) = ℤ.-≤+ {zero}{n} ℤ+-mono ℤ.-≤- {m}{n₁} n≤m
ℤ.+≤+ {suc m} {zero} () ℤ+-mono ℤ.-≤- n≤m
ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) ℤ+-mono ℤ.-≤- {zero} {zero} n≤m = ℤ.+≤+ m≤n
ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) ℤ+-mono ℤ.-≤- {suc m₁} {zero} z≤n = ℤ.-≤+ {m₁}{zero} ℤ+-mono ℤ.+≤+ m≤n
ℤ.+≤+ {suc m} {suc n} (s≤s m≤n) ℤ+-mono ℤ.-≤- {suc m₁} {suc n₁} (s≤s n≤m) = ℤ.-≤- n≤m ℤ+-mono ℤ.+≤+ m≤n
ℤ.+≤+ m≤n ℤ+-mono ℤ.+≤+ m≤n₁ = ℤ.+≤+ (m≤n +-mono m≤n₁)

--postulate _ℤ+-mono_ :  ℤ._+_ Preserves₂ ℤ._≤_ ⟶ ℤ._≤_ ⟶ ℤ._≤_

_ℚ+-mono_ :  _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
_ℚ+-mono_ {p}{q}{x}{y} (*≤* pq) (*≤* xy) = *≤* (begin
  (pn ℤ.* xd ℤ.+ xn ℤ.* pd) ℤ.* (qd ℤ.* yd)
  ∼⟨ ≡⇒≤ (proj₂ ℤdistrib (qd ℤ.* yd) (pn ℤ.* xd) (xn ℤ.* pd))   ⟩
  pn ℤ.* xd ℤ.* (qd ℤ.* yd) ℤ.+ xn ℤ.* pd ℤ.* (qd ℤ.* yd) 
  ∼⟨ ≡⇒≤ (cong₂ ℤ._+_ (ℤ*-assoc pn xd (qd ℤ.* yd)) (ℤ*-assoc xn pd (qd ℤ.* yd))) ⟩
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
  pn ℤ.* qd ℤ.* (+ (suc xd-1 ℕ.* suc yd-1)) ℤ.+ xn ℤ.* (yd ℤ.* (pd ℤ.* qd))
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
     
