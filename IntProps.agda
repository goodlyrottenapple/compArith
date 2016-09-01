module IntProps where

open import Data.Empty
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Nat
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
open import Data.Nat.Properties

open import Data.Integer as Int using (ℤ; +_; sign; _⊖_) renaming (_*_ to _ℤ*_; _+_ to _ℤ+_; _-_ to _ℤ-_; _≤_ to _ℤ≤_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)


open import NatProps

-_ : ℕ -> ℤ
- x = Int.- (+ x)


m⊖n≡mℤ-n : ∀ m n → m ⊖ n ≡ + m ℤ- + n
m⊖n≡mℤ-n zero zero = refl
m⊖n≡mℤ-n zero (suc n) = refl
m⊖n≡mℤ-n (suc m) zero rewrite m+0≡m {m} | m+0≡m {m} = refl
m⊖n≡mℤ-n (suc m) (suc n) = refl

⊖-≥ : ∀ {m n} → m ≥ n → m ⊖ n ≡ + (m ∸ n)
⊖-≥ z≤n       = refl
⊖-≥ (s≤s n≤m) = ⊖-≥ n≤m

⊖-< : ∀ {m n} → m < n → m ⊖ n ≡ - (n ∸ m)
⊖-< {zero}  (s≤s z≤n) = refl
⊖-< {suc m} (s≤s m<n) = ⊖-< m<n

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
