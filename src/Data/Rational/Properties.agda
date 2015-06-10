module Data.Rational.Properties where

open import Data.Sum
open import Relation.Nullary.Decidable
open import Data.Rational as ℚ using (ℚ; -_ ; _*_; _÷suc_; _-_; _+_; ∣_∣; decTotalOrder; _≤_; *≤* ; _≤?_; _÷_; _≃_)
open import Data.Integer as ℤ using (ℤ; +_ ; -[1+_]) renaming (_-_ to ℤ_-_; _+_ to _ℤ+_; _*_ to  _ℤ*_;_≤_ to ℤ_≤_)
open import Data.Nat as ℕ using (ℕ; suc; zero; compare; z≤n; _+⋎_; pred) renaming (_≤_ to ℕ_≤_)
open import Data.Nat.Properties.Simple using (+-comm; +-suc; +-right-identity; *-comm)
open import Relation.Binary.Core using (_≡_; refl; Sym; Rel; Reflexive; _Preserves₂_⟶_⟶_; IsEquivalence)
open import Data.Nat.Properties using (m≤m+n; cancel-+-left-≤; _+-mono_; _*-mono_)
open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality.Core using (trans; subst)
open import Algebra using (module CommutativeRing; Ring; module CommutativeMonoid; module AbelianGroup)
open import Data.Integer.Properties using (commutativeRing; abs-◃)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; subst; cong; cong₂)
open import Data.Product
open CommutativeRing commutativeRing
  using ()
  renaming (distrib to ℤdistrib; +-assoc to ℤ+-assoc; *-assoc to ℤ*-assoc; *-comm to ℤ*-comm; +-comm to ℤ+-comm; +-isAbelianGroup to ℤ-+-isAbelianGroup; *-identity to ℤ*-identity)

--Various lemmas about rational numbers

--Lemmas helping to show symmetry of the equivalence relation defined on the real numbers
⊖-swap : ∀ a b → a ℤ.⊖ b ≡ ℤ.- (b ℤ.⊖ a)
⊖-swap zero    zero    = refl
⊖-swap (suc _) zero    = refl
⊖-swap zero    (suc _) = refl
⊖-swap (suc a) (suc b) = ⊖-swap a b

ℤ-swap : (a b : ℤ) -> (ℤ.- (a ℤ.- b) ≡ b ℤ.- a)
ℤ-swap -[1+ n ] -[1+ n₁ ] = P.sym (⊖-swap n n₁)
ℤ-swap -[1+ n ] (+ zero) = refl
ℤ-swap -[1+ n ] (+ suc n₁) = trans (cong (λ a -> + suc (suc a)) (+-comm n n₁)) (cong (λ a -> + a) (P.sym (+-suc (suc n₁) n)))
ℤ-swap (+ zero) -[1+ n₁ ] = refl
ℤ-swap (+ suc n) -[1+ n₁ ] = cong (λ a -> -[1+ a ]) (+-comm n (suc n₁))
ℤ-swap (+ zero) (+ zero) = refl
ℤ-swap (+ zero) (+ suc n₁) = cong (λ a -> + a) (P.sym (+-right-identity (suc n₁)))
ℤ-swap (+ suc n) (+ zero) = cong (λ a -> -[1+ a ]) (+-right-identity n)
ℤ-swap (+ suc n) (+ suc n₁) = P.sym (⊖-swap n₁ n)

ℚ-swap : (x y : ℚ) -> (- (y - x) ≡ x - y)
ℚ-swap (-[1+ n₁ ] ÷suc d₁) (-[1+ n₂ ] ÷suc d₂) = cong₂ (λ a b -> (a ÷suc (pred b))) (ℤ-swap (-[1+ n₂ ] ℤ.* + suc d₁) (-[1+ n₁ ] ℤ.* + suc d₂)) (*-comm (suc d₂) (suc d₁))
ℚ-swap (-[1+ n₁ ] ÷suc d₁) ((+ zero) ÷suc d₂) = cong (λ a -> (-[1+ n₁ ] ℤ.* (+ suc d₂)) ℚ.÷suc (pred a))(*-comm (suc d₂) (suc d₁))
ℚ-swap (-[1+ n₁ ] ÷suc d₁) ((+ suc n₂) ÷suc d₂) = cong₂ (λ a b -> (a ÷suc (pred b))) (ℤ-swap (+ suc n₂ ℤ.* + suc d₁) (-[1+ n₁ ] ℤ.* + suc d₂)) (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ zero) ÷suc d₁) (-[1+ n₂ ] ÷suc d₂) = cong₂ (λ a b -> (a ÷suc (pred b))) (ℤ-swap (-[1+ n₂ ] ℤ.* + suc d₁) (+ zero ℤ.* + suc d₂)) (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ suc n₁) ÷suc d₁) (-[1+ n₂ ] ÷suc d₂) = cong₂ (λ a b -> (a ÷suc (pred b))) (ℤ-swap (-[1+ n₂ ] ℤ.* + suc d₁) (+ suc n₁ ℤ.* + suc d₂)) (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ zero) ÷suc d₁) ((+ zero) ÷suc d₂) = cong (λ a -> ((+ zero) ÷suc (pred a)))(*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ zero) ÷suc d₁) ((+ suc n₂) ÷suc d₂) = cong₂ (λ a b -> (a ÷suc (pred b))) (ℤ-swap (+ suc n₂ ℤ.* + suc d₁) (+ zero ℤ.* + suc d₂)) (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ suc n) ÷suc d₁) ((+ zero) ÷suc d₂) = cong₂ (λ a b -> (a ÷suc (pred b))) (ℤ-swap (+ zero ℤ.* + suc d₁) (+ suc n ℤ.* + suc d₂)) (*-comm (suc d₂) (suc d₁))
ℚ-swap ((+ suc n₁) ÷suc d₁) ((+ suc n₂) ÷suc d₂) = cong₂ (λ a b -> (a ÷suc (pred b))) (ℤ-swap (+ suc n₂ ℤ.* + suc d₁) (+ suc n₁ ℤ.* + suc d₂)) (*-comm (suc d₂) (suc d₁))

_⁻¹ : (n : ℕ) -> {≢0 : False (ℕ._≟_ n 0)} -> ℚ
(n ⁻¹) {≢0} = ((+ 1) ÷ n) {≢0}

ℚabs₁ : (x : ℚ) -> (∣ ℚ.- x ∣ ≡ ∣ x ∣)
ℚabs₁ (-[1+ n ] ÷suc d₁) = refl
ℚabs₁ ((+ zero) ÷suc d₁) = refl
ℚabs₁ ((+ suc n) ÷suc d₁) = refl

ℚabs₂ : (x y : ℚ) -> (∣ x - y ∣ ≡ ∣ y - x ∣)
ℚabs₂ x y = trans (cong ∣_∣ (P.sym (ℚ-swap x y) ))(ℚabs₁ (y - x))


--Since the we have defined rationals without requireming coprimality, our equivalence relation, ≈, is not synonymous with ≡ and therefore we cannot use subst or cong to modify expressions. Instead, we have to show for every function defined on rationals that it preserves the equality relation.
+-exist :  _+_ Preserves₂ _≃_ ⟶ _≃_ ⟶ _≃_
+-exist {p}{q}{x}{y} pq xy =  begin 
        (pn ℤ.* xd ℤ.+ xn ℤ.* pd) ℤ.* (qd ℤ.* yd) ≡⟨ proj₂ ℤdistrib (qd ℤ.* yd) (pn ℤ.* xd) (xn ℤ.* pd)   ⟩
        pn ℤ.* xd ℤ.* (qd ℤ.* yd) ℤ.+ xn ℤ.* pd ℤ.* (qd ℤ.* yd) ≡⟨ cong₂ ℤ._+_ (ℤ*-assoc pn xd (qd ℤ.* yd)) (ℤ*-assoc xn pd (qd ℤ.* yd)) ⟩
        pn ℤ.* (xd ℤ.* (qd ℤ.* yd)) ℤ.+ xn ℤ.* (pd ℤ.* (qd ℤ.* yd)) ≡⟨ cong₂ (λ a b -> pn ℤ.* a ℤ.+ xn ℤ.* (pd ℤ.* b)) (P.sym (ℤ*-assoc xd qd yd)) (ℤ*-comm qd yd) ⟩
        pn ℤ.* (xd ℤ.* qd ℤ.* yd) ℤ.+ xn ℤ.* (pd ℤ.* (yd ℤ.* qd)) ≡⟨ cong₂ (λ a b -> pn ℤ.* (a ℤ.* yd) ℤ.+ xn ℤ.* b) (ℤ*-comm xd qd) (P.sym (ℤ*-assoc pd yd qd)) ⟩
        pn ℤ.* (qd ℤ.* xd ℤ.* yd) ℤ.+ xn ℤ.* (pd ℤ.* yd ℤ.* qd) ≡⟨ cong₂ (λ a b -> pn ℤ.* a ℤ.+ xn ℤ.* (b ℤ.* qd)) (ℤ*-assoc qd xd yd) (ℤ*-comm pd yd) ⟩
        pn ℤ.* (qd ℤ.* (xd ℤ.* yd)) ℤ.+ xn ℤ.* (yd ℤ.* pd ℤ.* qd) ≡⟨ cong₂ (λ a b -> a ℤ.+ xn ℤ.* b) (P.sym (ℤ*-assoc pn qd (xd ℤ.* yd))) (ℤ*-assoc yd pd qd) ⟩
        pn ℤ.* qd ℤ.* (xd ℤ.* yd) ℤ.+ xn ℤ.* (yd ℤ.* (pd ℤ.* qd)) ≡⟨ cong₂ (λ a b -> a ℤ.* (xd ℤ.* yd) ℤ.+ b) pq  ((P.sym (ℤ*-assoc xn yd (pd ℤ.* qd)))) ⟩
        qn ℤ.* pd ℤ.* (xd ℤ.* yd) ℤ.+ xn ℤ.* yd ℤ.* (pd ℤ.* qd) ≡⟨ cong₂ (λ a b -> a ℤ.+ b ℤ.* (pd ℤ.* qd)) (ℤ*-assoc qn pd (xd ℤ.* yd)) xy ⟩
        qn ℤ.* (pd ℤ.* (xd ℤ.* yd)) ℤ.+ yn ℤ.* xd ℤ.* (pd ℤ.* qd) ≡⟨ cong₂ (λ a b -> qn ℤ.* (pd ℤ.* a) ℤ.+ yn ℤ.* xd ℤ.* b) (ℤ*-comm xd yd) (ℤ*-comm pd qd) ⟩
        qn ℤ.* (pd ℤ.* (yd ℤ.* xd)) ℤ.+ yn ℤ.* xd ℤ.* (qd ℤ.* pd) ≡⟨ cong₂ (λ a b -> qn ℤ.* a ℤ.+ b) (P.sym (ℤ*-assoc pd yd xd )) (ℤ*-assoc yn xd (qd ℤ.* pd)) ⟩
        qn ℤ.* (pd ℤ.* yd ℤ.* xd) ℤ.+ yn ℤ.* (xd ℤ.* (qd ℤ.* pd)) ≡⟨ cong₂ (λ a b -> qn ℤ.* (a ℤ.* xd) ℤ.+ yn ℤ.* b) (ℤ*-comm pd yd) (P.sym (ℤ*-assoc xd qd pd )) ⟩
        qn ℤ.* (yd ℤ.* pd ℤ.* xd) ℤ.+ yn ℤ.* (xd ℤ.* qd ℤ.* pd) ≡⟨ cong₂ (λ a b -> qn ℤ.* a ℤ.+ yn ℤ.* (b ℤ.* pd)) (ℤ*-assoc yd pd xd) (ℤ*-comm xd qd) ⟩
        qn ℤ.* (yd ℤ.* (pd ℤ.* xd)) ℤ.+ yn ℤ.* (qd ℤ.* xd ℤ.* pd) ≡⟨ cong₂ (λ a b -> a ℤ.+ yn ℤ.* b) (P.sym (ℤ*-assoc qn yd (pd ℤ.* xd))) (ℤ*-assoc qd xd pd) ⟩
        qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* (qd ℤ.* (xd ℤ.* pd)) ≡⟨ cong (λ a -> qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* (qd ℤ.* a)) (ℤ*-comm xd pd) ⟩
        qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* (qd ℤ.* (pd ℤ.* xd)) ≡⟨ cong (λ a -> qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ a) (P.sym (ℤ*-assoc yn qd (pd ℤ.* xd))) ⟩
        qn ℤ.* yd ℤ.* (pd ℤ.* xd) ℤ.+ yn ℤ.* qd ℤ.* (pd ℤ.* xd) ≡⟨ P.sym (proj₂ ℤdistrib (pd ℤ.* xd) (qn ℤ.* yd) (yn ℤ.* qd)) ⟩
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

+-red₁ : (n : ℕ) -> ((+ 1) ÷suc (suc (n ℕ.+ n)) ℚ.+ (+ 1) ÷suc (suc (n ℕ.+ n)) ℚ.≃ (+ 1) ÷suc n)
+-red₁ n = begin 
      ((+ 1) ℤ.* k ℤ.+ (+ 1) ℤ.* k) ℤ.* + suc n ≡⟨ cong (λ a -> ((a ℤ.+ a) ℤ.* + suc n)) (proj₁ ℤ*-identity k) ⟩
      (k ℤ.+ k) ℤ.* + suc n ≡⟨ cong (λ a -> a ℤ.* + suc n) (P.sym (lem k)) ⟩
      (+ 2) ℤ.* k ℤ.* (+ suc n) ≡⟨ cong (λ a -> a ℤ.* + suc n) (ℤ*-comm (+ 2) k) ⟩
      k ℤ.* (+ 2) ℤ.* (+ suc n) ≡⟨ ℤ*-assoc k (+ 2) (+ suc n) ⟩
      k ℤ.* ((+ 2) ℤ.* (+ suc n)) ≡⟨ cong (λ a -> k ℤ.* a) (lem (+ suc n)) ⟩
      k ℤ.* (+ suc (n ℕ.+ suc n)) ≡⟨ cong (λ a -> k ℤ.* + suc a) (+-comm n (suc n)) ⟩
      k ℤ.* k ≡⟨ P.sym (proj₁ ℤ*-identity (k ℤ.* k)) ⟩
      (+ 1) ℤ.* (k ℤ.* k)
    ∎
    where
      open P.≡-Reasoning
      k = + suc (suc (n ℕ.+ n))
      lem : (j : ℤ) -> ((+ 2) ℤ.* j ≡ j ℤ.+ j)
      lem j = trans (proj₂ ℤdistrib j (+ 1) (+ 1)) (cong₂ ℤ._+_ (proj₁ ℤ*-identity j) (proj₁ ℤ*-identity j)) 

+-red₂ : (n : ℕ) -> (((+ 1) ÷suc (suc ((suc (n ℕ.+ n)) ℕ.+ (suc (n ℕ.+ n)))) + (+ 1) ÷suc (suc ((suc (n ℕ.+ n)) ℕ.+ (suc (n ℕ.+ n))))) + ((+ 1) ÷suc (suc ((suc (n ℕ.+ n)) ℕ.+ (suc (n ℕ.+ n)))) + (+ 1) ÷suc (suc ((suc (n ℕ.+ n)) ℕ.+ (suc (n ℕ.+ n))))) ℚ.≃ ((+ 1) ÷suc n))
+-red₂ n = IsEquivalence.trans ℚ.isEquivalence {start} {middle} {end} (+-exist {1÷k + 1÷k}{1÷j}{1÷k + 1÷k}{1÷j} (+-red₁ j) (+-red₁ j)) (+-red₁ n)
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

postulate _ℚ+-mono_ :  _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
