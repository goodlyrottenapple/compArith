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

open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Agda.Builtin.Nat using ( div-helper ; mod-helper )
open import Data.Nat.DivMod
open DivMod

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



toℕ≤ : ∀ {a : ℕ} {fa : Fin (suc a)} -> (toℕ fa) ≤ a
toℕ≤ {zero} {zero} = z≤n
toℕ≤ {zero} {suc ()}
toℕ≤ {suc a} {zero} = z≤n
toℕ≤ {suc a} {suc fa} = s≤s toℕ≤


acc≤div-helper : ∀ {acc m a n} -> acc ≤ div-helper acc m a n
acc≤div-helper {acc} {m} {zero}  {n} = ≤-refl refl
acc≤div-helper {acc} {m} {suc a} {zero} = start
  acc ≤⟨ ≤′⇒≤ (≤′-step ≤′-refl) ⟩
  suc acc ≤⟨ acc≤div-helper {suc acc} {m} {a} {m} ⟩
  div-helper (suc acc) m a m □
acc≤div-helper {acc} {m} {suc a} {suc n} = acc≤div-helper {acc} {m} {a} {n}

≤div-helper : ∀ {acc n a b m} -> a ≤ b -> div-helper acc n a m ≤ div-helper acc n b m
≤div-helper {acc} {n} {zero}  {zero} _ = ≤-refl refl
≤div-helper {acc} {n} {zero}  {suc b} {m} _ = acc≤div-helper {acc} {n} {suc b} {m}
≤div-helper {acc} {n} {suc a} {suc b} {zero} (s≤s a≤b) = ≤div-helper a≤b
≤div-helper {acc} {n} {suc a} {suc b} {suc m} (s≤s a≤b) = ≤div-helper a≤b

a*1≡a : ∀ {a} -> a * 1 ≡ a
a*1≡a {zero} = refl
a*1≡a {suc a} = cong suc a*1≡a


mod-helper≡0' : ∀ {acc a b} -> b ≤ a -> mod-helper acc a (suc b) b ≡ 0
mod-helper≡0' {acc} {zero}  {zero}  _ = refl
mod-helper≡0' {acc} {zero}  {suc b} ()
mod-helper≡0' {acc} {suc a} {zero}  b≤a = refl
mod-helper≡0' {acc} {suc a} {suc b} (s≤s b≤a) = mod-helper≡0' {suc acc} {suc a} {b} (≤-step b≤a)


mod-helper≡0'' : ∀ {k m b c} -> mod-helper k m (suc b + c) b ≡ mod-helper (b + k) m (2 + c) 1
mod-helper≡0'' {k} {m} {zero}  {c} = refl
mod-helper≡0'' {k} {m} {suc b} {c} = begin
  mod-helper k m (suc (suc b) + c) (suc b) ≡⟨ ih ⟩
  mod-helper (b + (suc k)) m (2 + c) 1 ≡⟨ cong (λ x → mod-helper x m (2 + c) 1) {b + suc k} {suc b + k} (b+sk≡sb+k {b} {k}) ⟩
  mod-helper (suc b + k) m (2 + c) 1 ∎
  where
  open Data.Nat.Properties.SemiringSolver

  ih : mod-helper (suc k) m (suc b + c) b ≡ mod-helper (b + (suc k)) m (2 + c) 1
  ih = mod-helper≡0'' {suc k} {m} {b} {c}

  b+sk≡sb+k : ∀ {b k} -> b + suc k ≡ suc b + k
  b+sk≡sb+k {b} {k} = solve 2 (λ b k -> b :+ (con 1 :+ k) := (con 1 :+ b) :+ k) refl b k



mod-helper≡0 : ∀ {a c} -> mod-helper 0 a ((suc c) * (suc a)) a ≡ 0
mod-helper≡0 {zero}  {zero} = refl
mod-helper≡0 {zero}  {suc c} = mod-helper≡0 {zero} {c}
mod-helper≡0 {suc a} {zero} = begin
  mod-helper 1 (suc a) (suc (a + zero)) a ≡⟨ cong (λ x → mod-helper 1 (suc a) x a) {suc (a + zero)} {suc a} (m+0≡m {suc a}) ⟩
  mod-helper 1 (suc a) (suc a) a ≡⟨ mod-helper≡0' {1} {suc a} {a} (≤-step (≤-refl refl)) ⟩
  0 ∎
mod-helper≡0 {suc a} {suc c} = begin
  mod-helper 0 (suc a) ((2 + c) * (2 + a)) (suc a) ≡⟨ refl ⟩
  mod-helper 0 (suc a) ((2 + a) + ((1 + c) * (2 + a))) (suc a) ≡⟨ mod-helper≡0'' {0} {suc a} {suc a} ⟩
  mod-helper 0 (suc a)            ((1 + c) * (2 + a)) (suc a) ≡⟨ ih ⟩
  0 ∎
  where
  ih : mod-helper 0 (suc a) ((suc c) * suc (suc a)) (suc a) ≡ 0
  ih = mod-helper≡0 {suc a} {c}


to-fromℕ≤″ : ∀ m {n} {p : m <″ n} → toℕ (Data.Fin.fromℕ≤″ m p) ≡ m
to-fromℕ≤″ zero {zero} {less-than-or-equal ()}
to-fromℕ≤″ zero {suc n} {less-than-or-equal refl} = refl
to-fromℕ≤″ (suc m) {zero} {less-than-or-equal ()}
to-fromℕ≤″ (suc m) {suc .(suc (m + _))} {less-than-or-equal refl} = cong suc (to-fromℕ≤″ m)

mod≡0 : ∀ {a b} -> toℕ ((suc a * suc b) mod (suc b)) ≡ 0
mod≡0 {a} {b} = begin
  toℕ ((suc a * suc b) mod (suc b)) ≡⟨ to-fromℕ≤″ (mod-helper 0 b (suc a * suc b) b) ⟩
  mod-helper 0 b (suc a * suc b) b  ≡⟨ mod-helper≡0 {b} {a} ⟩ 0 ∎



suc-inj : ∀{b c : ℕ} → 1 + b ≡ 1 + c → b ≡ c
suc-inj {b} {.b} refl = refl

+-inj : ∀(a : ℕ) {b c : ℕ} → a + b ≡ a + c → b ≡ c
+-inj zero refl = refl
+-inj (suc a) a+b≡a+c = +-inj a (suc-inj a+b≡a+c)

*-inj : ∀{a b c : ℕ} → (suc a) * (suc c) ≡ b * (suc c) → suc a ≡ b
*-inj {zero}  {zero}        {c} ()
*-inj {zero}  {suc zero}    {c} refl = refl
*-inj {zero}  {suc (suc b)} {c} r rewrite m+0≡m {c} = ⊥-elim (≡-bot r)
  where
  ≡-bot : ∀{x y : ℕ} -> x ≡ x + (suc y) -> ⊥
  ≡-bot {zero} ()
  ≡-bot {suc x} {y} sx≡sx+y = ≡-bot {x} {y} (suc-inj sx≡sx+y)
*-inj {suc a} {zero}        {c} ()
*-inj {suc a} {suc b}       {c} r = cong suc (*-inj {a} {b} {c} (+-inj (suc c) r))


≡div : ∀ {a b} -> (a * (suc b)) div (suc b) ≡ a
≡div {zero}  {b} = refl
≡div {suc a} {b} = sym lemma
  where
  lemma₁ : (suc a * suc b) ≡ ((suc a * suc b) div (suc b)) * (suc b)
  lemma₁ = begin
    (suc a * suc b) ≡⟨ property ((suc a * suc b) divMod (suc b)) ⟩
    toℕ ((suc a * suc b) mod (suc b)) + ((suc a * suc b) div (suc b)) * (suc b) ≡⟨ m+n≡m'+n' {toℕ (suc a * suc b mod suc b)} {0} (mod≡0 {a} {b}) refl ⟩
    ((suc a * suc b) div (suc b)) * (suc b) ∎

  lemma : suc a ≡ (suc a * suc b) div (suc b)
  lemma = *-inj lemma₁
