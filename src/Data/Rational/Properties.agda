module Data.Rational.Properties where

open import Function
open import Data.Sum
open import Data.Empty
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
open import Data.Rational as ℚ using (ℚ; -_ ; _*_; _÷suc_;
  _-_; _+_; ∣_∣; decTotalOrder; _≤_; *≤* ; _≤?_; _÷_; _≃_;
  isEquivalence; drop-*≤*; ≡⇒≃ )
open import Level renaming (zero to Levelzero; suc to Levelsuc)
open import Data.Integer as ℤ using (decTotalOrder; ℤ; +_ ;
  -[1+_]; _≤?_; _⊖_; ◃-cong; ◃-left-inverse; sign; drop‿+≤+) renaming 
  (_-_ to ℤ_-_; _+_ to _ℤ+_; _*_ to  _ℤ*_;_≤_ to ℤ_≤_; _<_ to _ℤ<_;
   _>_ to _ℤ>_)
open import Data.Nat as ℕ using (ℕ; suc; zero; pred; compare;
  _∸_; s≤s; z≤n; _≥_; decTotalOrder)
    renaming (_≤_ to ℕ_≤_; _≤?_ to _≤??_; _<_ to _ℕ<_)
open import Data.Nat.Properties.Simple using (+-suc;
  *-comm; +-right-identity; +-*-suc)
  renaming (+-comm to ℕ+-comm)
open import Relation.Binary.Core
open import Data.Nat.Properties using (m≤m+n; ≤-steps;
  ≤-step; ≤⇒pred≤; ≤pred⇒≤; pred-mono; n≤1+n; _*-mono_; 1+n≰n)
  renaming (_+-mono_ to _ℕ+-mono_)
import Relation.Binary.PreorderReasoning as Pre
import Data.Integer.Addition.Properties as Add
open import Relation.Binary.PropositionalEquality.Core
  using (trans; subst)
open import Algebra
import Algebra.FunctionProperties
open import Data.Integer.Properties using (commutativeRing; abs-◃;
  *-+-right-mono; cancel-*-+-right-≤; n⊖n≡0; ∣-∣-≤)
  renaming (_+-mono_ to _ℤ+-mono_; -swap to ℤ-swap; ≰⇒> to ℤ≰⇒>;
  ≤⇒pred≤ to ℤ≤⇒pred≤)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; 
  subst; cong; cong₂; subst₂)
open import Data.Product
open import Relation.Binary using (module DecTotalOrder)
open CommutativeRing commutativeRing
  using ()
  renaming (distrib to ℤdistrib; +-assoc to ℤ+-assoc; *-assoc to ℤ*-assoc;
  *-comm to ℤ*-comm; +-comm to ℤ+-comm; *-identity to ℤ*-identity)
open CommutativeMonoid Add.commutativeMonoid
  using ()
  renaming (identity to ℤ+-identity)
open DecTotalOrder ℕ.decTotalOrder using () renaming (refl to ≤-refl)

open Algebra.FunctionProperties (_≃_)

--Various properties of rational numbers
_⁻¹ : (n : ℕ) -> {≢0 : False (ℕ._≟_ n 0)} -> ℚ
(n ⁻¹) {≢0} = ((+ 1) ÷ n) {≢0}

--Properties of addition on rationals

+-comm : Commutative _+_
+-comm (n₁ ÷suc d₁)(n₂ ÷suc d₂) = cong₂ ℤ._*_ (ℤ+-comm (n₁ ℤ.* + suc d₂)
  (n₂ ℤ.* + suc d₁)) (ℤ*-comm (+ suc d₂)(+ suc d₁))

+-identity : Identity ((+ 0)÷suc 0) _+_
+-identity = (left-identity , right-identity)
  where
  open P.≡-Reasoning
  open IsEquivalence ℚ.isEquivalence using ()
      renaming (sym to ℚsym; trans to ℚtrans)

  right-identity : RightIdentity  ((+ 0)÷suc 0) _+_
  right-identity (n ÷suc d) = begin
    (n ℤ.* (+ 1) ℤ.+ + 0 ℤ.* + suc d) ℤ.* + suc d  ≡⟨ cong (λ a -> a ℤ.* + suc d)
      (proj₂ ℤ+-identity (n ℤ.* (+ 1))) ⟩
    n ℤ.* (+ 1) ℤ.* + suc d ≡⟨ ℤ*-assoc n (+ 1) (+ suc d) ⟩
    n ℤ.* (+ 1 ℤ.* + suc d) ≡⟨ cong (λ a -> n ℤ.* a) (ℤ*-comm (+ 1)(+ suc d)) ⟩
    (n ℤ.* (+ suc d ℤ.* + 1) ∎)

  left-identity : LeftIdentity ((+ 0)÷suc 0) _+_
  left-identity q = ℚtrans {(+ 0)÷suc 0 + q}{q + (+ 0)÷suc 0}{q}
    (+-comm ((+ 0)÷suc 0) q)(right-identity q)

+-assoc : Associative _+_
+-assoc (n₁ ÷suc d₁)  (n₂ ÷suc d₂) (n₃ ÷suc d₃) = begin
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

--Lemmas needed to show symmetry of the equivalence relation 
--defined on the real numbers

-swap : (x y : ℚ) -> (- (y - x) ≡ x - y)
-swap (-[1+ n₁ ] ÷suc d₁) (-[1+ n₂ ] ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (-[1+ n₂ ] ℤ.* + suc d₁) (-[1+ n₁ ] ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
-swap (-[1+ n₁ ] ÷suc d₁) ((+ zero) ÷suc d₂) = 
  cong (λ a -> (-[1+ n₁ ] ℤ.* (+ suc d₂)) ℚ.÷suc (pred a))
  (*-comm (suc d₂) (suc d₁))
-swap (-[1+ n₁ ] ÷suc d₁) ((+ suc n₂) ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (+ suc n₂ ℤ.* + suc d₁) (-[1+ n₁ ] ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
-swap ((+ zero) ÷suc d₁) (-[1+ n₂ ] ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (-[1+ n₂ ] ℤ.* + suc d₁) (+ zero ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
-swap ((+ suc n₁) ÷suc d₁) (-[1+ n₂ ] ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (-[1+ n₂ ] ℤ.* + suc d₁) (+ suc n₁ ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
-swap ((+ zero) ÷suc d₁) ((+ zero) ÷suc d₂) = 
  cong (λ a -> ((+ zero) ÷suc (pred a)))
  (*-comm (suc d₂) (suc d₁))
-swap ((+ zero) ÷suc d₁) ((+ suc n₂) ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (+ suc n₂ ℤ.* + suc d₁) (+ zero ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
-swap ((+ suc n) ÷suc d₁) ((+ zero) ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (+ zero ℤ.* + suc d₁) (+ suc n ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))
-swap ((+ suc n₁) ÷suc d₁) ((+ suc n₂) ÷suc d₂) = 
  cong₂ (λ a b -> (a ÷suc (pred b))) 
  (ℤ-swap (+ suc n₂ ℤ.* + suc d₁) (+ suc n₁ ℤ.* + suc d₂)) 
  (*-comm (suc d₂) (suc d₁))

ℚabs₁ : (x : ℚ) -> (∣ - x ∣ ≡ ∣ x ∣)
ℚabs₁ (-[1+ n ] ÷suc d₁) = refl
ℚabs₁ ((+ zero) ÷suc d₁) = refl
ℚabs₁ ((+ suc n) ÷suc d₁) = refl

ℚabs₂ : (x y : ℚ) -> (∣ x - y ∣ ≡ ∣ y - x ∣)
ℚabs₂ x y = trans (cong ∣_∣ (P.sym (-swap x y) ))(ℚabs₁ (y - x))


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
  ≡⟨ cong (λ a -> k ℤ.* + suc a) (ℕ+-comm n (suc n)) ⟩
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
+-red₂ n = ℚtrans {start} {middle}{end} 
  (+-exist {1÷k + 1÷k}{1÷j}{1÷k + 1÷k}{1÷j} (+-red₁ j) (+-red₁ j)) 
    (+-red₁ n)
  where
    open IsEquivalence ℚ.isEquivalence using ()
      renaming (trans to ℚtrans)
    j = suc (n ℕ.+ n)
    k = suc (j ℕ.+ j)
    1÷j = (+ 1) ÷suc j
    1÷k = (+ 1) ÷suc k
    start = (1÷k + 1÷k) + (1÷k + 1÷k)
    middle = 1÷j + 1÷j
    end = (+ 1) ÷suc n

ℚ≤lem : {m n : ℕ} -> ((+ 1) ÷suc (m ℕ.+ n) ≤ (+ 1) ÷suc m)
ℚ≤lem {m}{n} =  *≤* (ℤ.+≤+ (ℕ.s≤s ((m≤m+n m n) ℕ+-mono (z≤n))))

_+-mono_ :  _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
_+-mono_ {p}{q}{x}{y} (*≤* pq) (*≤* xy) = *≤* (begin
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

ℚ≤-abs₂ : {x y : ℚ} -> (x ≤ y) -> ∣ y - x ∣ ℚ.≃ y - x
ℚ≤-abs₂ {x}{y} le = ℚtrans {∣ y - x ∣}{∣ x - y ∣}{y - x}
  (≡⇒≃ (ℚabs₂ y x)) (ℚ≤-abs₁ le)
  where
  open IsEquivalence ℚ.isEquivalence using ()
       renaming (trans to ℚtrans)

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

data _<_ : ℚ → ℚ → Set where
  *≤* : ∀ {p q} →
        (ℚ.numerator p ℤ.* (+ suc (ℚ.denominator-1 q))) ℤ<
        (ℚ.numerator q ℤ.* (+ suc (ℚ.denominator-1 p))) →
        p < q

_>_ : Rel ℚ Level.zero
m > n = n < m

_≰_ : Rel ℚ Level.zero
a ≰ b = ¬ a ≤ b

≰⇒> : _≰_ ⇒ _>_
≰⇒> ¬p = *≤* (ℤ≰⇒> (λ z → ¬p (*≤* z)))

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (*≤* le) = *≤* (ℤ≤⇒pred≤ _ _ le)

triang : (x y z : ℚ) -> (∣ x - z ∣ ≤ ∣ x - y ∣ + ∣ y - z ∣)
triang x y z with x ℚ.≤? y | y ℚ.≤? z | x ℚ.≤? z
triang x y z | yes p | yes p₁ | yes p₂ = begin
  ∣ x - z ∣   ∼⟨ ≡⇒≤ (ℚ≤-abs₁ p₂)   ⟩
  z - x ∼⟨ ≡⇒≤ (P.sym (proj₂ +-identity (z - x))) ⟩
  (z - x) + ((+ 0) ÷suc 0) ∼⟨  ≡⇒≤ {(z - x)}{(z - x)} refl
  +-mono ≡⇒≤ {(+ 0) ÷suc 0}{(y - y)}
  (ℚsym {y - y}{(+ 0) ÷suc 0} (x-x {y})) ⟩
  (z - x) + (y - y) ∼⟨ ≡⇒≤ {z - x}{ - x + z} (+-comm z (- x))
  +-mono (≡⇒≤ {(y - y)}{(y - y)} refl)   ⟩
  - x + z + (y - y) ∼⟨ ≡⇒≤ (+-assoc (- x) z (y - y) )   ⟩
  - x + (z + (y - y)) ∼⟨ ≡⇒≤ { - x}{ - x} refl
  +-mono ≡⇒≤ {z + (y - y)}{z + y - y}
  (ℚsym {z + y - y}{z + (y - y)} (+-assoc z y (- y)) )   ⟩
  - x + (z + y - y) ∼⟨ ≡⇒≤ { - x}{ - x} refl +-mono
  (≡⇒≤ {z + y}{y + z} (+-comm z y )
  +-mono ≡⇒≤ { - y}{ - y} refl)   ⟩
  - x + (y + z - y) ∼⟨ ≡⇒≤ { - x}{ - x} refl
  +-mono ≡⇒≤ {y + z - y}{y + (z - y)} (+-assoc y z (- y) )   ⟩
  - x + (y + (z - y)) ∼⟨ ≡⇒≤ { - x + (y + (z - y))}{ - x + y + (z - y)}
  (ℚsym { - x + y + (z - y)}{ - x + (y + (z - y))}
  (+-assoc (- x) y (z - y) ))   ⟩
  - x + y + (z - y) ∼⟨ ≡⇒≤ { - x + y}{y - x}
  (+-comm (- x) y) +-mono ≡⇒≤ {z - y}{z - y} refl  ⟩
  (y - x) + (z - y) ∼⟨  ≡⇒≤ {y - x}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{y - x}
  (ℚ≤-abs₁ {x}{y} p)) +-mono ≡⇒≤ {z - y}{∣ y - z ∣}
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
  z - x ∼⟨ ≡⇒≤ (P.sym (proj₂ +-identity (z - x))) ⟩
  (z - x) + ((+ 0) ÷suc 0) ∼⟨  ≡⇒≤ {(z - x)}{(z - x)} refl +-mono
  ≡⇒≤ {(+ 0) ÷suc 0}{(z - z)}(ℚsym {z - z}{(+ 0) ÷suc 0} (x-x {z})) ⟩
  z - x + (z - z) ∼⟨ ((<⇒≤ (≰⇒> ¬p)) +-mono ≡⇒≤ { - x}{ - x} refl)
  +-mono ((<⇒≤ (≰⇒> ¬p)) +-mono ≡⇒≤ { - z}{ - z} refl) ⟩
  (y - x) + (y - z) ∼⟨  ≡⇒≤ {y - x}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{y - x}
  (ℚ≤-abs₁ {x}{y} p)) +-mono ≡⇒≤ {y - z}{∣ y - z ∣}
  (ℚsym {∣ y - z ∣}{y - z} (ℚ≤-abs₂ (<⇒≤ (≰⇒> ¬p))))⟩
  ∣ x - y ∣ + ∣ y - z ∣ ∎ 
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
triang x y z | yes p | no ¬p | no ¬p₁ = begin
  ∣ x - z ∣   ∼⟨ ≡⇒≤ (ℚ≤-abs₂ (<⇒≤ (≰⇒> ¬p₁))) ⟩
  (x - z) ∼⟨   ≡⇒≤ (P.sym (proj₁ +-identity (x - z)))  ⟩
  (+ 0) ÷suc 0 + (x - z) ∼⟨  ≡⇒≤ {(+ 0) ÷suc 0}{x - x}
  (ℚsym {x - x}{(+ 0) ÷suc 0} (x-x {x})) +-mono ≡⇒≤ {x - z}{x - z} refl ⟩
  (x - x) + (x - z) ∼⟨  (p  +-mono ≡⇒≤ { - x}{ - x} refl ) +-mono
  (p +-mono ≡⇒≤ { - z}{ - z} refl) ⟩
  (y - x) + (y - z) ∼⟨  ≡⇒≤ {y - x}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{y - x}
  (ℚ≤-abs₁ p)) +-mono ≡⇒≤ {y - z}{∣ y - z ∣} (ℚsym {∣ y - z ∣}{y - z}
  (ℚ≤-abs₂ (<⇒≤ (≰⇒> ¬p))))⟩ 
  ∣ x - y ∣ + ∣ y - z ∣ ∎ 
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
triang x y z | no ¬p | yes p | yes p₁ = begin
  ∣ x - z ∣                 ∼⟨ ≡⇒≤ (ℚ≤-abs₁ p₁)   ⟩
  z - x                    ∼⟨ ≡⇒≤ (P.sym (proj₂ +-identity (z - x))) ⟩
  (z - x) + ((+ 0) ÷suc 0) ∼⟨  ≡⇒≤ {(z - x)}{(z - x)} refl
  +-mono ≡⇒≤ {(+ 0) ÷suc 0}{(y - y)}(ℚsym {y - y}{(+ 0)÷suc 0}(x-x {y}))⟩
  z - x + (y - y)          ∼⟨ ≡⇒≤ (+-assoc z (- x) (y - y)) ⟩
  z + (- x + (y - y))      ∼⟨ ≡⇒≤ {z}{z} refl +-mono
  ≡⇒≤ { - x + (y - y)}{ - x + y - y}
  (ℚsym { - x + y - y}{ - x + (y - y)} (+-assoc (- x) y (- y))) ⟩
  z + (- x + y - y)        ∼⟨ ≡⇒≤ {z}{z} refl +-mono
  ((≡⇒≤ { - x}{ - x} refl  +-mono  (<⇒≤ (≰⇒> ¬p)))
  +-mono (≡⇒≤ { - y}{ - y} refl)) ⟩
  z + (- x + x - y)        ∼⟨ ≡⇒≤ {z}{z} refl +-mono
  (≡⇒≤ { - x + x}{(+ 0)÷suc 0} (ℚtrans { - x + x}{x - x}{(+ 0)÷suc 0}
  (+-comm (- x) x) (x-x {x})) +-mono ≡⇒≤ { - y}{ - y} refl) ⟩
  z + ((+ 0)÷suc 0 - y) ∼⟨ ≡⇒≤ {z}{z} refl +-mono
  ≡⇒≤ {((+ 0)÷suc 0 - y)}{ - y} (proj₁ +-identity (- y)) ⟩
  z - y ∼⟨ ≡⇒≤  (ℚsym {(+ 0) ÷suc 0 + (z - y)}{z - y}(proj₁ +-identity (z - y))) ⟩
  ((+ 0) ÷suc 0) + (z - y) ∼⟨ ≡⇒≤ {(+ 0) ÷suc 0}{(y - y)}
  (ℚsym {y - y}{(+ 0) ÷suc 0}(x-x {y})) +-mono ≡⇒≤ {z - y}{z - y} refl ⟩
  y - y + (z - y) ∼⟨ (<⇒≤ (≰⇒> ¬p) +-mono ≡⇒≤ { - y}{ - y} refl)
  +-mono ≡⇒≤ {z - y}{z - y} refl ⟩
  x - y + (z - y) ∼⟨ ≡⇒≤ {x - y}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{x - y}
  (ℚ≤-abs₂ (<⇒≤ (≰⇒> ¬p)))) +-mono ≡⇒≤ {z - y}{∣ y - z ∣}
  (ℚsym {∣ y - z ∣}{z - y} (ℚ≤-abs₁ p)) ⟩
  ∣ x - y ∣ + ∣ y - z ∣ ∎ 
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
triang x y z | no ¬p | yes p | no ¬p₁ = begin
  ∣ x - z ∣   ∼⟨ ≡⇒≤ (ℚ≤-abs₂ (<⇒≤ (≰⇒> ¬p₁)))   ⟩
  x - z ∼⟨ ≡⇒≤ (ℚsym {x - z + (+ 0)÷suc 0}{x - z}(proj₂ +-identity (x - z))) ⟩
  (x - z) + ((+ 0) ÷suc 0) ∼⟨  ≡⇒≤ {x - z}{x - z} refl
  +-mono ≡⇒≤ {(+ 0) ÷suc 0}{(y - y)}(ℚsym {y - y}{(+ 0)÷suc 0}(x-x {y}))⟩
  x - z + (y - y) ∼⟨ ≡⇒≤ (+-assoc x (- z) (y - y)) ⟩
  x + (- z + (y - y)) ∼⟨ ≡⇒≤ {x}{x} refl +-mono
  ≡⇒≤ { - z + (y - y)}{ - z + y - y}
  (ℚsym { - z + y - y}{ - z + (y - y)} (+-assoc (- z) y (- y))) ⟩
  x + (- z + y - y) ∼⟨ ≡⇒≤ {x}{x} refl +-mono ((≡⇒≤ { - z}{ - z} refl
  +-mono p)  +-mono (≡⇒≤ { - y}{ - y} refl)) ⟩
  x + (- z + z - y) ∼⟨ ≡⇒≤ {x}{x} refl +-mono
  (≡⇒≤ { - z + z}{(+ 0)÷suc 0} (ℚtrans { - z + z}{z - z}{(+ 0)÷suc 0}
  (+-comm (- z) z) (x-x {z})) +-mono ≡⇒≤ { - y}{ - y} refl) ⟩
  x + ((+ 0) ÷suc 0 - y) ∼⟨ ≡⇒≤ {x}{x} refl +-mono
  ≡⇒≤ {(+ 0)÷suc 0 - y}{ - y} (proj₁ +-identity (- y)) ⟩
  x - y ∼⟨ ≡⇒≤ (ℚsym {x - y + (+ 0) ÷suc 0}{x - y} (proj₂ +-identity (x - y))) ⟩
  x - y + (+ 0) ÷suc 0 ∼⟨ ≡⇒≤ {x - y}{x - y} refl +-mono
  ≡⇒≤ {(+ 0) ÷suc 0}{y - y}(ℚsym {y - y}{(+ 0) ÷suc 0} (x-x {y})) ⟩
  x - y + (y - y) ∼⟨ ≡⇒≤ {x - y}{x - y} refl +-mono
  (p +-mono ≡⇒≤ { - y}{ - y} refl) ⟩
  x - y + (z - y) ∼⟨ ≡⇒≤ {x - y}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{x - y}
  (ℚ≤-abs₂ (<⇒≤ (≰⇒> ¬p)))) +-mono ≡⇒≤ {z - y}{∣ y - z ∣}
  (ℚsym {∣ y - z ∣}{z - y} (ℚ≤-abs₁ p)) ⟩
  ∣ x - y ∣ + ∣ y - z ∣ ∎
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
triang x y z | no ¬p | no ¬p₁ | yes p =
  ⊥-elim (¬p (≤trans p (<⇒≤ (≰⇒> ¬p₁))))
  where
  open DecTotalOrder ℚ.decTotalOrder using ()
      renaming (trans to ≤trans)
triang x y z | no ¬p | no ¬p₁ | no ¬p₂ = begin 
  ∣ x - z ∣             ∼⟨ ≡⇒≤ (ℚ≤-abs₂ (<⇒≤ (≰⇒> ¬p₂)))   ⟩
  x - z                ∼⟨ ≡⇒≤ {x}{x + (+ 0)÷suc 0}
  (ℚsym {x + (+ 0)÷suc 0}{x} (proj₂ +-identity x)) +-mono ≡⇒≤ { - z}{ - z} refl ⟩
  x + (+ 0) ÷suc 0 - z ∼⟨ (≡⇒≤ {x}{x} refl  +-mono
  ≡⇒≤ {(+ 0)÷suc 0}{y - y} (ℚsym {y - y}{(+ 0)÷suc 0} (x-x {y}))) +-mono
  ≡⇒≤ { - z}{ - z} refl ⟩
  x + (y - y) - z      ∼⟨ (≡⇒≤ {x}{x} refl  +-mono
  ≡⇒≤ {y - y}{ - y + y} (+-comm y (- y))) +-mono ≡⇒≤ { - z}{ - z}refl ⟩
  x + (- y + y) - z    ∼⟨ ≡⇒≤ {x + (- y + y)}{x - y + y}
  (ℚsym {x - y + y}{x + (- y + y)}(+-assoc x (- y) y)) +-mono
    ≡⇒≤ { - z}{ - z} refl ⟩
  x - y + y - z        ∼⟨ ≡⇒≤ { x - y + y - z}{x - y + (y - z)}
    (+-assoc (x - y) y (- z)) ⟩
  x - y + (y - z)      ∼⟨ ≡⇒≤ {x - y}{∣ x - y ∣}(ℚsym {∣ x - y ∣}{x - y}
    (ℚ≤-abs₂ (<⇒≤ (≰⇒> ¬p)))) +-mono
    ≡⇒≤ {y - z}{∣ y - z ∣}(ℚsym {∣ y - z ∣}{y - z}(ℚ≤-abs₂ (<⇒≤ (≰⇒> ¬p₁))))⟩  
  ∣ x - y ∣ + ∣ y - z ∣ ∎
     where
     open IsEquivalence ℚ.isEquivalence using ()
       renaming (sym to ℚsym; trans to ℚtrans)
     open DecTotalOrder ℚ.decTotalOrder using (preorder)
       renaming (reflexive to ≡⇒≤)
     open Pre preorder
