module CompArith where

open import Data.Bool
open import Data.Nat
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple

open import Data.Integer as Int using (ℤ; +_; sign; _⊖_) renaming (_*_ to _ℤ*_; _+_ to _ℤ+_; _-_ to _ℤ-_; _≤_ to _ℤ≤_)

open import Algebra
import Data.Integer.Properties as IntegerProp
private
  module CR = CommutativeRing IntegerProp.commutativeRing


-- open Int.≤-Reasoning
--   renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)

open import Data.Vec
open import Data.Sign using (Sign)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning

-_ : ℕ -> ℤ
- x = Int.- (+ x)

𝔹 = Bool

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc x = m * (m ^ x)

-- ∥_∥ : 𝔹 -> ℤ
-- ∥ false ∥ = + 0
-- ∥ true ∥ = + 1

compl : ∀ {k} -> Vec 𝔹 (ℕ.suc k) -> Vec 𝔹 (ℕ.suc k)
compl {zero} (x ∷ []) = not x ∷ []
compl {suc k} (x ∷ xs) = not x ∷ compl xs

Σ : ∀ {k} -> Vec 𝔹 k -> ℕ
Σ {zero} [] = 0
Σ {suc i} (false ∷ xs) = Σ xs
Σ {suc i} (true ∷ xs) = (2 ^ i) + Σ xs

⟦_⟧ : ∀ {k} -> Vec 𝔹 (ℕ.suc k) -> ℤ
⟦ xs ⟧ = + Σ xs

⟪_⟫ : ∀ {k} -> Vec 𝔹 (ℕ.suc k) -> ℤ
⟪_⟫ {k} (false ∷ xs) = + Σ xs
⟪_⟫ {k} (true ∷ xs) = - (2 ^ k) ℤ+ (+ Σ xs)

σ : ∀ {k} -> Vec 𝔹 (ℕ.suc k) -> Sign
σ (false ∷ xs) = Sign.+
σ (true ∷ xs) = Sign.-

Top : ∀ {k} -> Vec 𝔹 k
Top {zero} = []
Top {suc k} = true ∷ Top

≤-steps2 : ∀ {m n} k → m ≤ n → k + m ≤ k + n
≤-steps2 zero m≤n = m≤n
≤-steps2 (suc k) m≤n = s≤s (≤-steps2 k m≤n)

≤-Top : ∀ {k} {x : Vec 𝔹 k} -> Σ x ≤ Σ (Top {k})
≤-Top {zero} {[]} = z≤n
≤-Top {suc k} {false ∷ xs} = ≤-steps {Σ xs} {Σ {k} Top} (2 ^ k) (≤-Top {k})
≤-Top {suc k} {true ∷ xs} = ≤-steps2 (2 ^ k) (≤-Top {k})

+-zer-id : ∀ n -> n + 0 ≡ n
+-zer-id zero = refl
+-zer-id (suc n) = cong suc (+-zer-id n)

*-1-id : ∀ n -> 1 * n ≡ n
*-1-id zero = refl
*-1-id (suc n) = cong suc (*-1-id n)

≤-*-steps : ∀ {m n} k → 1 ≤ k -> m ≤ n → m ≤ k * n
≤-*-steps zero () _
≤-*-steps {n = n} (suc zero) 1≤k m≤n rewrite *-1-id n = m≤n
≤-*-steps {n = n} (suc (suc k)) 1≤k m≤n = ≤-steps n (≤-*-steps (suc k) (s≤s z≤n) m≤n)

1≤2^k : ∀ {k} -> 1 ≤ (2 ^ k)
1≤2^k {zero} = s≤s z≤n
1≤2^k {suc k} = start
  1 ≤⟨ 1≤2^k {k} ⟩
  2 ^ k ≤⟨ ≤-*-steps {n = 2 ^ k} 2 (s≤s z≤n) (≤′⇒≤ ≤′-refl) ⟩
  2 ^ (suc k) □

lem1-1-1 : ∀ {k} -> Σ (Top {k}) ≡ (2 ^ k) ∸ 1 -- equiv to ⟦ Top {k} ⟧ ≡ (2 ^ k) ∸ 1
lem1-1-1 {zero} = refl
lem1-1-1 {suc k} rewrite lem1-1-1 {k} | +-right-identity (2 ^ k) = begin
  (2 ^ k) + ((2 ^ k) ∸ 1) ≡⟨ sym (+-∸-assoc (2 ^ k) {2 ^ k} {1} (1≤2^k {k})) ⟩ refl


⊖-ℤ- : ∀ m n → m ⊖ n ≡ + m ℤ- + n
⊖-ℤ- zero zero = refl
⊖-ℤ- zero (suc n) = refl
⊖-ℤ- (suc m) zero rewrite +-zer-id m | +-zer-id m = refl
⊖-ℤ- (suc m) (suc n) = refl

⊖-≥ : ∀ {m n} → m ≥ n → m ⊖ n ≡ + (m ∸ n)
⊖-≥ z≤n       = refl
⊖-≥ (s≤s n≤m) = ⊖-≥ n≤m

-- +-swap : ∀ k n -> (suc k) + n ≡ (suc n) + k
-- +-swap zero n rewrite +-zer-id (suc n) = refl
-- +-swap (suc k) n = cong suc (+-comm (suc k) n)

-- ≤'-steps : ∀ {m n} k → m ℤ≤ n → k ℤ+ m ℤ≤ k ℤ+ n
-- ≤'-steps {+_ m} {+_ n} (+_ k) m≤n = Int.+≤+ (≤-steps2 k (Int.drop‿+≤+ m≤n))
-- ≤'-steps {+_ m} {Int.-[1+_] n} (+_ k) ()
-- ≤'-steps {Int.-[1+_] m} {+_ n} (+_ zero) Int.-≤+ = Int.-≤+
-- ≤'-steps {Int.-[1+_] zero} {+_ n} (+_ (suc k)) Int.-≤+ = Int.+≤+ aux
--   where
--   aux : k ≤ suc k + n
--   aux rewrite +-swap k n = ≤-steps (suc n) (≤′⇒≤ ≤′-refl)
-- ≤'-steps {Int.-[1+_] (suc m)} {+_ n} (+_ (suc k)) Int.-≤+ = {!   !}
-- ≤'-steps {Int.-[1+_] m} {Int.-[1+_] n} (+_ k) (Int.-≤- n≤m) = {!   !}
-- ≤'-steps (Int.-[1+_] k) m≤n = {!   !}

ℤ≤-steps : ∀ {m n} k → m ℤ≤ n → k ℤ+ m ℤ≤ k ℤ+ n
ℤ≤-steps {+ m} {+ n} (+ k)          (Int.+≤+ m≤n) = Int.+≤+ (≤-steps2 k m≤n)
ℤ≤-steps {+ m} {+ n} (Int.-[1+ k ]) (Int.+≤+ m≤n) = {!   !}

ℤ≤-steps {+ m}          {Int.-[1+ n ]} k ()
ℤ≤-steps {Int.-[1+ m ]} {+ n}          k Int.-≤+ = {!   !}
ℤ≤-steps {Int.-[1+ m ]} {Int.-[1+ n ]} k (Int.-≤- n≤m) = {!   !}


lem1-1 : ∀ {k} {x : Vec 𝔹 (suc k)} -> sign ⟪ x ⟫ ≡ σ x
lem1-1 {k} {false ∷ xs} = refl
lem1-1 {k} {true ∷ xs} = aux₂ (- (2 ^ k) ℤ+ + Σ xs) aux
  where
  aux₁ : - (2 ^ k) ℤ+ + ((2 ^ k) ∸ 1) ≡ - 1
  aux₁ = begin
    - (2 ^ k) ℤ+ + ((2 ^ k) ∸ 1) ≡⟨ cong (_ℤ+_ (- (2 ^ k))) (sym (⊖-≥ (1≤2^k {k}))) ⟩
    - (2 ^ k) ℤ+ ((2 ^ k) ⊖ 1) ≡⟨ cong (_ℤ+_ (- (2 ^ k))) (⊖-ℤ- (2 ^ k) 1) ⟩
    - (2 ^ k) ℤ+ (+ (2 ^ k) ℤ+ - 1) ≡⟨ sym (CR.+-assoc (- (2 ^ k)) (+ (2 ^ k)) (- 1)) ⟩
    (- (2 ^ k) ℤ+ + (2 ^ k)) ℤ+ - 1 ≡⟨ CR.+-comm (- (2 ^ k) ℤ+ + (2 ^ k)) (- 1) ⟩
    - 1 ℤ+ (- (2 ^ k) ℤ+ + (2 ^ k)) ≡⟨ cong (_ℤ+_ (- 1)) (CR.+-comm (- (2 ^ k)) (+ (2 ^ k))) ⟩
    - 1 ℤ+ (+ (2 ^ k) ℤ- + (2 ^ k)) ≡⟨ cong (_ℤ+_ (- 1)) (sym (⊖-ℤ- (2 ^ k) (2 ^ k))) ⟩
    - 1 ℤ+ ((2 ^ k) ⊖ (2 ^ k)) ≡⟨ cong (_ℤ+_ (- 1)) (IntegerProp.n⊖n≡0 (2 ^ k)) ⟩
    - 1 ∎

  aux₂ : ∀ x -> x ℤ≤ - 1 -> sign x ≡ Sign.-
  aux₂ (+_ n) ()
  aux₂ (Int.-[1+_] n) x≤ℤ-1 = refl

  aux : ⟪ true ∷ xs ⟫ ℤ≤ - 1
  aux rewrite sym aux₁ | sym (lem1-1-1 {k}) = ℤ≤-steps (- (2 ^ k)) (Int.+≤+ (≤-Top {k}))
