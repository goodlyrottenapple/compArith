module NatProps where

open import Data.Nat
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc x = m * (m ^ x)

-- modaux : ℕ -> ℕ -> ℕ -> ℕ
-- modaux zero b acc = acc
-- modaux (suc a) b acc with b ≟ (suc acc)
-- modaux (suc a) b acc | yes _ = modaux a b 0
-- modaux (suc a) b acc | no _ = modaux a b (suc acc)
--
-- _mod_ : ℕ -> ℕ -> ℕ
-- a mod b = modaux a b 0
--


m+0≡m : ∀ {m} -> m + 0 ≡ m
m+0≡m {0} = refl
m+0≡m {suc m} = cong suc (m+0≡m {m})

m+n≡m'+n' : ∀ {m m' n n'} -> m ≡ m' -> n ≡ n' -> m + n ≡ m' + n'
m+n≡m'+n' refl refl = refl

1*m≡m : ∀ {m} -> 1 * m ≡ m
1*m≡m {0} = refl
1*m≡m {suc m} = cong suc (1*m≡m {m})

2^k+2^k≡2^sk : ∀ {k} -> (2 ^ k) + (2 ^ k) ≡ 2 ^ (suc k)
2^k+2^k≡2^sk {0} = refl
2^k+2^k≡2^sk {suc k} rewrite m+0≡m {2 ^ k} | m+0≡m {(2 ^ k) + (2 ^ k)} = refl

≤-refl : ∀ {m n} → m ≡ n → m ≤ n
≤-refl refl = ≤′⇒≤ ≤′-refl


≤-steps2 : ∀ {m n} k → m ≤ n → k + m ≤ k + n
≤-steps2 zero m≤n = m≤n
≤-steps2 (suc k) m≤n = s≤s (≤-steps2 k m≤n)


≤-steps3 : ∀ {m n} (o p : ℕ) → m ≤ n → o ≤ p → o + m ≤ p + n
≤-steps3 {m} {n} zero p m≤n z≤n = start m ≤⟨ m≤n ⟩ n ≤⟨ m≤m+n n p ⟩ n + p ≤⟨ ≤-refl (+-comm n p) ⟩ p + n □
≤-steps3 {m} {n} (suc o) (suc p) m≤n (s≤s o≤p) = s≤s (≤-steps3 o p m≤n o≤p)


≤-*-steps : ∀ {m n} k → 1 ≤ k -> m ≤ n → m ≤ k * n
≤-*-steps zero () _
≤-*-steps {n = n} (suc zero) 1≤k m≤n rewrite 1*m≡m {n} = m≤n
≤-*-steps {n = n} (suc (suc k)) 1≤k m≤n = ≤-steps n (≤-*-steps (suc k) (s≤s z≤n) m≤n)


1≤2^k : ∀ {k} -> 1 ≤ (2 ^ k)
1≤2^k {zero} = s≤s z≤n
1≤2^k {suc k} = start
  1 ≤⟨ 1≤2^k {k} ⟩
  2 ^ k ≤⟨ ≤-*-steps {n = 2 ^ k} 2 (s≤s z≤n) (≤′⇒≤ ≤′-refl) ⟩
  2 ^ (suc k) □


¬≤-> : ∀ {m n} -> ¬ (m ≤ n) -> m > n
¬≤-> {0} {n} ¬m≤n = ⊥-elim (¬m≤n z≤n)
¬≤-> {suc m} {0} ¬m≤n = s≤s z≤n
¬≤-> {suc m} {suc n} ¬m≤n = s≤s (¬≤-> (λ z → ¬m≤n (s≤s z)))


>-¬≤ : ∀ {m n} -> m > n -> ¬ (m ≤ n)
>-¬≤ (s≤s z≤n) ()
>-¬≤ (s≤s (s≤s m>n)) (s≤s m≤n) = >-¬≤ m≤n m>n


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

-- use ≤-pred
-- sx≤sy⇒x≤y : ∀ {x y} -> suc x ≤ suc y -> x ≤ y
-- sx≤sy⇒x≤y (s≤s x≤y) = x≤y


k-m≤k : ∀ k m -> k ∸ m ≤ k
k-m≤k 0 0 = z≤n
k-m≤k 0 (suc m) = z≤n
k-m≤k (suc k) 0 = s≤s (k-m≤k k zero)
k-m≤k (suc k) (suc m) = start k ∸ m ≤⟨ k-m≤k k m ⟩ k ≤⟨ ≤′⇒≤ (≤′-step ≤′-refl) ⟩ suc k □
