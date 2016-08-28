module CompArith where

open import Data.Empty
open import Data.Bool
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Nat
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple

open import Data.Integer as Int using (ℤ; +_; sign; _⊖_) renaming (_*_ to _ℤ*_; _+_ to _ℤ+_; _-_ to _ℤ-_; _≤_ to _ℤ≤_)

open import Algebra
import Data.Integer.Properties as IntegerProp
private
  module CRℤ = CommutativeRing IntegerProp.commutativeRing


-- open Int.≤-Reasoning
--   renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)

open import Data.Vec
open import Data.Sign using (Sign)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)

-_ : ℕ -> ℤ
- x = Int.- (+ x)

𝔹 = Bool

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc x = m * (m ^ x)

∥_∥ : 𝔹 -> ℕ
∥ false ∥ = 0
∥ true ∥ = 1

compl : ∀ {k} -> Vec 𝔹 (ℕ.suc k) -> Vec 𝔹 (ℕ.suc k)
compl {zero} (x ∷ []) = not x ∷ []
compl {suc k} (x ∷ xs) = not x ∷ compl xs

Σ : ∀ {k} -> Vec 𝔹 k -> ℕ
Σ {zero} [] = 0
Σ {suc i} (false ∷ xs) = Σ xs
Σ {suc i} (true ∷ xs) = (2 ^ i) + Σ xs

Σspec : ∀ {k} -> Vec 𝔹 k -> ℕ
Σspec {zero} [] = 0
Σspec {suc i} (x ∷ xs) = ∥ x ∥ * 2 ^ i + Σ xs

+-zer-id : ∀ n -> n + 0 ≡ n
+-zer-id zero = refl
+-zer-id (suc n) = cong suc (+-zer-id n)

*-1-id : ∀ n -> 1 * n ≡ n
*-1-id zero = refl
*-1-id (suc n) = cong suc (*-1-id n)


-- Σ is a better def. to work with ... similar to the def. of ⟪_⟫
Σspec≡Σ : ∀ {k} (x : Vec 𝔹 k) -> Σspec x ≡ Σ x
Σspec≡Σ [] = refl
Σspec≡Σ (false ∷ xs) = refl
Σspec≡Σ {suc i} (true ∷ xs) rewrite *-1-id (2 ^ i) = refl

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

⊖-< : ∀ {m n} → m < n → m ⊖ n ≡ - (n ∸ m)
⊖-< {zero}  (s≤s z≤n) = refl
⊖-< {suc m} (s≤s m<n) = ⊖-< m<n

¬≤-> : ∀ {m n} -> ¬ (m ≤ n) -> m > n
¬≤-> {0} {n} ¬m≤n = ⊥-elim (¬m≤n z≤n)
¬≤-> {suc m} {0} ¬m≤n = s≤s z≤n
¬≤-> {suc m} {suc n} ¬m≤n = s≤s (¬≤-> (λ z → ¬m≤n (s≤s z)))

>-¬≤ : ∀ {m n} -> m > n -> ¬ (m ≤ n)
>-¬≤ (s≤s z≤n) ()
>-¬≤ (s≤s (s≤s m>n)) (s≤s m≤n) = >-¬≤ m≤n m>n

-∃ : ∀ {k n} -> k > n -> ∃(λ m -> - (k ∸ n) ≡ Int.-[1+ m ] × k ∸ n ≡ suc m)
-∃ {0} k>n = ⊥-elim (>-¬≤ k>n z≤n)
-∃ {suc k} {0} k>n = k , refl , refl
-∃ {suc k} {suc n} (s≤s k>n) = m , left , right
  where
  ih : ∃(λ m → - (k ∸ n) ≡ Int.-[1+ m ] × k ∸ n ≡ suc m)
  ih = -∃ k>n

  m = proj₁ ih
  left = proj₁ (proj₂ ih)
  right = proj₂ (proj₂ ih)


ℤ≤-refl : ∀ {m n} → m ≡ n → m ℤ≤ n
ℤ≤-refl {+ m}          {+ .m}          refl = Int.+≤+ (≤′⇒≤ ≤′-refl)
ℤ≤-refl {+ m}          {Int.-[1+ n ]}  ()
ℤ≤-refl {Int.-[1+ m ]} {+ n}           ()
ℤ≤-refl {Int.-[1+ m ]} {Int.-[1+ .m ]} refl = Int.-≤- (≤′⇒≤ ≤′-refl)

≤-refl : ∀ {m n} → m ≡ n → m ≤ n
≤-refl refl = ≤′⇒≤ ≤′-refl


m≤n⇒m-k≤n-k : ∀ {m n} k -> m ≤ n -> m ∸ k ≤ n ∸ k
m≤n⇒m-k≤n-k 0 m≤n = m≤n
m≤n⇒m-k≤n-k {0} (suc k) m≤n = z≤n
m≤n⇒m-k≤n-k {suc m} {0} (suc k) ()
m≤n⇒m-k≤n-k {suc m} {suc n} (suc k) (s≤s m≤n) = m≤n⇒m-k≤n-k k m≤n


n≤m⇒k-m≤k-n : ∀ m n k -> n ≤ m -> k ∸ m ≤ k ∸ n
n≤m⇒k-m≤k-n 0 n 0 _ = z≤n
n≤m⇒k-m≤k-n (suc m) n 0 _ = z≤n
n≤m⇒k-m≤k-n 0 0 (suc k) n≤m = s≤s (n≤m⇒k-m≤k-n 0 0 k n≤m)
n≤m⇒k-m≤k-n zero (suc n) (suc k) ()
n≤m⇒k-m≤k-n (suc m) 0 (suc k) z≤n = start
  k ∸ m ≤⟨ n≤m⇒k-m≤k-n m 0 k z≤n ⟩ k ≤⟨ ≤′⇒≤ (≤′-step ≤′-refl) ⟩ suc k □
n≤m⇒k-m≤k-n (suc m) (suc n) (suc k) (s≤s n≤m) = n≤m⇒k-m≤k-n m n k n≤m

sx≤sy⇒x≤y : ∀ {x y} -> suc x ≤ suc y -> x ≤ y
sx≤sy⇒x≤y (s≤s x≤y) = x≤y

k-m≤k : ∀ k m -> k ∸ m ≤ k
k-m≤k 0 0 = z≤n
k-m≤k 0 (suc m) = z≤n
k-m≤k (suc k) 0 = s≤s (k-m≤k k zero)
k-m≤k (suc k) (suc m) = start k ∸ m ≤⟨ k-m≤k k m ⟩ k ≤⟨ ≤′⇒≤ (≤′-step ≤′-refl) ⟩ suc k □


ℤ≤-steps : ∀ {m n} k → m ℤ≤ n → k ℤ+ m ℤ≤ k ℤ+ n
ℤ≤-steps {+ m}          {+ n}          (+ k)                (Int.+≤+ m≤n) = Int.+≤+ (≤-steps2 k m≤n)
ℤ≤-steps {+ 0}          {+ 0}          (Int.-[1+ k ])       (Int.+≤+ m≤n) = ℤ≤-refl refl
ℤ≤-steps {+ 0}          {+ suc n}      (Int.-[1+ 0 ])       (Int.+≤+ m≤n) = Int.-≤+
ℤ≤-steps {+ 0}          {+ suc n}      (Int.-[1+ suc k ])   (Int.+≤+ m≤n) with suc k ≤? n
ℤ≤-steps {+ 0}          {+ suc _}      (Int.-[1+ suc k ])   (Int.+≤+ m≤n) | yes (s≤s {_} {n} k≤n)
  rewrite ⊖-≥ {n} {k} k≤n = Int.-≤+
ℤ≤-steps {+ 0}          {+ suc n}      (Int.-[1+ suc k ])   (Int.+≤+ m≤n) | no sk>n
  rewrite ⊖-< {n} {suc k} (¬≤-> sk>n) = body
  where
  ∃m = -∃ (¬≤-> sk>n)
  m = proj₁ ∃m
  m≡- = proj₁ (proj₂ ∃m)
  m≡ = proj₂ (proj₂ ∃m)

  aux₁ : ∀ {k n} -> k ∸ n ≤ k
  aux₁ {n = 0} = ≤′⇒≤ ≤′-refl
  aux₁ {0} {suc n} = z≤n
  aux₁ {suc k} {suc n} = start
    suc k ∸ suc n ≤⟨ aux₁ {k} {n} ⟩ k ≤⟨ ≤′⇒≤ (≤′-step ≤′-refl) ⟩ suc k □

  aux : m ≤ suc k
  aux = start
    m ≤⟨ ≤′⇒≤ (≤′-step ≤′-refl) ⟩ suc m ≤⟨ ≤-refl (sym m≡) ⟩ suc k ∸ n ≤⟨ aux₁ {suc k} {n} ⟩ suc k □

  body : Int.-[1+ suc k ] ℤ≤ - (suc k ∸ n)
  body rewrite m≡- = Int.-≤- aux

ℤ≤-steps {+ suc m}      {+ 0}          (Int.-[1+ k ])     (Int.+≤+ ())
ℤ≤-steps {+ suc m}      {+ suc n}      (Int.-[1+ 0 ])     (Int.+≤+ (s≤s m≤n)) = Int.+≤+ m≤n
ℤ≤-steps {+ suc m}      {+ suc n}      (Int.-[1+ suc k ]) (Int.+≤+ m≤n) with suc k ≤? m | suc k ≤? n
ℤ≤-steps {+ suc _}      {+ suc _}      (Int.-[1+ suc k ]) (Int.+≤+ (s≤s (s≤s m≤n))) | yes (s≤s {_} {m} k≤m) | yes (s≤s {_} {n} k≤n)
  rewrite ⊖-≥ {m} {k} k≤m | ⊖-≥ {n} {k} k≤n = Int.+≤+ (m≤n⇒m-k≤n-k k m≤n)
ℤ≤-steps {+ suc _}      {+ suc n}      (Int.-[1+ suc k ]) (Int.+≤+ (s≤s m≤n)) | yes (s≤s {_} {m} k≤m) | no ¬sk≤n =
  ⊥-elim (¬sk≤n (start
    suc k ≤⟨ s≤s k≤m ⟩ suc m ≤⟨ m≤n ⟩ n □))
ℤ≤-steps {+ suc m}      {+ suc _}      (Int.-[1+ suc k ]) (Int.+≤+ (s≤s m≤sn)) | no ¬sk≤m | yes (s≤s {_} {n} k≤n)
  rewrite ⊖-< {m} {suc k} (¬≤-> ¬sk≤m) | ⊖-≥ {n} {k} k≤n | proj₁ (proj₂ (-∃ (¬≤-> ¬sk≤m))) = Int.-≤+
ℤ≤-steps {+ suc m}      {+ suc n}      (Int.-[1+ suc k ]) (Int.+≤+ (s≤s m≤n)) | no ¬sk≤m | no ¬sk≤n
  rewrite ⊖-< {m} {suc k} (¬≤-> ¬sk≤m) | ⊖-< {n} {suc k} (¬≤-> ¬sk≤n) = body
  where
  ∃m = -∃ (¬≤-> ¬sk≤m)
  m'≡- = proj₁ (proj₂ ∃m)
  m'≡ = proj₂ (proj₂ ∃m)
  ∃n = -∃ (¬≤-> ¬sk≤n)
  n'≡- = proj₁ (proj₂ ∃n)
  n'≡ = proj₂ (proj₂ ∃n)

  aux : suc (proj₁ ∃n) ≤ suc (proj₁ ∃m)
  aux rewrite (sym m'≡) | (sym n'≡) = n≤m⇒k-m≤k-n n m (suc k) m≤n

  body : - (suc k ∸ m) ℤ≤ - (suc k ∸ n)
  body rewrite m'≡- | n'≡- = Int.-≤- (sx≤sy⇒x≤y aux)

ℤ≤-steps {+ m}          {Int.-[1+ n ]} k ()
ℤ≤-steps {Int.-[1+ m ]} {+ n}          (+ k)              Int.-≤+ with suc m ≤? k
ℤ≤-steps {Int.-[1+ m ]} {+ n}          (+ _)              Int.-≤+ | yes (s≤s {_} {k} m≤k)
  rewrite ⊖-≥ {k} {m} m≤k = Int.+≤+ (start
    k ∸ m ≤⟨ k-m≤k k m ⟩ k ≤⟨ ≤′⇒≤ (≤′-step ≤′-refl) ⟩ suc k ≤⟨ m≤m+n (suc k) n ⟩ suc k + n □)
ℤ≤-steps {Int.-[1+ m ]} {+ n}          (+ k)              Int.-≤+ | no ¬sm≤k
  rewrite ⊖-< {k} {suc m} (¬≤-> ¬sm≤k) | proj₁ (proj₂ (-∃ (¬≤-> ¬sm≤k))) = Int.-≤+
ℤ≤-steps {Int.-[1+ m ]} {+ n}          (Int.-[1+ k ])     Int.-≤+ with suc k ≤? n
ℤ≤-steps {Int.-[1+ m ]} {+ _}          (Int.-[1+ k ])     Int.-≤+ | yes (s≤s {_} {n} k≤n)
  rewrite ⊖-≥ {n} {k} k≤n = Int.-≤+
ℤ≤-steps {Int.-[1+_] m} {+_ n} (Int.-[1+_] k) Int.-≤+ | no ¬sk≤n
  rewrite ⊖-< {n} {suc k} (¬≤-> ¬sk≤n) | proj₁ (proj₂ (-∃ (¬≤-> ¬sk≤n))) = Int.-≤- (sx≤sy⇒x≤y aux)
  where
  aux : suc (proj₁ (-∃ (¬≤-> ¬sk≤n))) ≤ suc (suc k) + m
  aux rewrite sym (proj₂ (proj₂ (-∃ (¬≤-> ¬sk≤n)))) = start
    suc k ∸ n ≤⟨ k-m≤k (suc k) n ⟩
    suc k ≤⟨ ≤′⇒≤ (≤′-step ≤′-refl) ⟩
    suc (suc k) ≤⟨ m≤m+n (suc (suc k)) m ⟩
    suc (suc k) + m □

ℤ≤-steps {Int.-[1+ m ]} {Int.-[1+ n ]} (+ k)              (Int.-≤- n≤m) with suc m ≤? k | suc n ≤? k
ℤ≤-steps {Int.-[1+ m ]} {Int.-[1+ n ]} (+ _)              (Int.-≤- n≤m) | yes (s≤s {_} {k} m≤k) | yes (s≤s n≤k)
  rewrite ⊖-≥ {k} {m} m≤k | ⊖-≥ {k} {n} n≤k = Int.+≤+ (n≤m⇒k-m≤k-n m n k n≤m)
ℤ≤-steps {Int.-[1+ m ]} {Int.-[1+ n ]} (+ _)              (Int.-≤- n≤m) | yes (s≤s {_} {k} m≤k) | no ¬sn≤sk =
  ⊥-elim (¬sn≤sk (s≤s (start n ≤⟨ n≤m ⟩ m ≤⟨ m≤k ⟩ k □)))
ℤ≤-steps {Int.-[1+ m ]} {Int.-[1+ n ]} (+ _)              (Int.-≤- n≤m) | no ¬sm≤k | yes (s≤s {_} {k} n≤k)
  rewrite ⊖-≥ {k} {n} n≤k | ⊖-< {k} {m} (¬≤-> (λ z → ¬sm≤k (s≤s z))) | proj₁ (proj₂ (-∃ (¬≤-> ¬sm≤k))) = Int.-≤+
ℤ≤-steps {Int.-[1+ m ]} {Int.-[1+ n ]} (+ k)              (Int.-≤- n≤m) | no ¬sm≤k | no ¬sn≤k
  rewrite ⊖-< {k} {suc m} (¬≤-> ¬sm≤k) | ⊖-< {k} {suc n} (¬≤-> ¬sn≤k) |
    proj₁ (proj₂ (-∃ (¬≤-> ¬sm≤k))) | proj₁ (proj₂ (-∃ (¬≤-> ¬sn≤k))) = Int.-≤- (sx≤sy⇒x≤y body)
    where
    body : suc (proj₁ (-∃ (¬≤-> ¬sn≤k))) ≤ suc (proj₁ (-∃ (¬≤-> ¬sm≤k)))
    body rewrite sym (proj₂ (proj₂ (-∃ (¬≤-> ¬sm≤k)))) | sym (proj₂ (proj₂ (-∃ (¬≤-> ¬sn≤k)))) =
      m≤n⇒m-k≤n-k k (s≤s n≤m)

ℤ≤-steps {Int.-[1+ m ]} {Int.-[1+ n ]} (Int.-[1+ k ])     (Int.-≤- n≤m) = Int.-≤- (s≤s (≤-steps2 k n≤m))



lem1-1 : ∀ {k} {x : Vec 𝔹 (suc k)} -> sign ⟪ x ⟫ ≡ σ x
lem1-1 {k} {false ∷ xs} = refl
lem1-1 {k} {true ∷ xs} = aux₂ (- (2 ^ k) ℤ+ + Σ xs) aux
  where
  aux₁ : - (2 ^ k) ℤ+ + ((2 ^ k) ∸ 1) ≡ - 1
  aux₁ = begin
    - (2 ^ k) ℤ+ + ((2 ^ k) ∸ 1) ≡⟨ cong (_ℤ+_ (- (2 ^ k))) (sym (⊖-≥ (1≤2^k {k}))) ⟩
    - (2 ^ k) ℤ+ ((2 ^ k) ⊖ 1) ≡⟨ cong (_ℤ+_ (- (2 ^ k))) (⊖-ℤ- (2 ^ k) 1) ⟩
    - (2 ^ k) ℤ+ (+ (2 ^ k) ℤ+ - 1) ≡⟨ sym (CRℤ.+-assoc (- (2 ^ k)) (+ (2 ^ k)) (- 1)) ⟩
    (- (2 ^ k) ℤ+ + (2 ^ k)) ℤ+ - 1 ≡⟨ CRℤ.+-comm (- (2 ^ k) ℤ+ + (2 ^ k)) (- 1) ⟩
    - 1 ℤ+ (- (2 ^ k) ℤ+ + (2 ^ k)) ≡⟨ cong (_ℤ+_ (- 1)) (CRℤ.+-comm (- (2 ^ k)) (+ (2 ^ k))) ⟩
    - 1 ℤ+ (+ (2 ^ k) ℤ- + (2 ^ k)) ≡⟨ cong (_ℤ+_ (- 1)) (sym (⊖-ℤ- (2 ^ k) (2 ^ k))) ⟩
    - 1 ℤ+ ((2 ^ k) ⊖ (2 ^ k)) ≡⟨ cong (_ℤ+_ (- 1)) (IntegerProp.n⊖n≡0 (2 ^ k)) ⟩
    - 1 ∎

  aux₂ : ∀ x -> x ℤ≤ - 1 -> sign x ≡ Sign.-
  aux₂ (+_ n) ()
  aux₂ (Int.-[1+_] n) x≤ℤ-1 = refl

  aux : ⟪ true ∷ xs ⟫ ℤ≤ - 1
  aux rewrite sym aux₁ | sym (lem1-1-1 {k}) = ℤ≤-steps (- (2 ^ k)) (Int.+≤+ (≤-Top {k}))
