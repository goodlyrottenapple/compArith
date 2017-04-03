module CompArithGen where

-- open import Data.Empty
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ≤; raise; reduce≥)
open import Data.Fin.Properties renaming (_≟_ to _≟F_)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Nat
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple

open import Data.Integer as Int using (ℤ; +_; sign; _⊖_) renaming (_*_ to _ℤ*_; _+_ to _ℤ+_; _-_ to _ℤ-_; _≤_ to _ℤ≤_)
open Int.≤-Reasoning
  renaming (begin_ to startℤ_; _∎ to _ℤ□; _≡⟨_⟩_ to _≡ℤ⟨_⟩_; _≤⟨_⟩_ to _ℤ≤⟨_⟩_)

open import Data.Vec
open import Data.Sign using (Sign)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning
open import Data.Empty
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Algebra
import Data.Integer.Properties as IntegerProp
private
  module CR = CommutativeRing IntegerProp.commutativeRing

private
  module CS = CommutativeSemiring Data.Nat.Properties.commutativeSemiring

open import Data.Nat.DivMod
open DivMod

open import NatProps
open import IntProps


open import Agda.Builtin.Nat using ( div-helper ; mod-helper )


Σ : ∀ {k d} -> Vec (Fin d) k -> ℕ
Σ {0} [] = 0
Σ {suc i} {D} (x ∷ xs) = toℕ x * D ^ i + Σ xs

⟦_⟧ : ∀ {k n} -> Vec (Fin n) (ℕ.suc k) -> ℕ
⟦ xs ⟧ = Σ xs



-- <-≠-suc : ∀ {a b} -> a < b -> ¬ (suc a ≡ b) -> suc a < b
-- <-≠-suc {zero} {zero} () suca≠b
-- <-≠-suc {zero} {suc zero} a<b suca≠b = ⊥-elim (suca≠b refl)
-- <-≠-suc {zero} {suc (suc b)} a<b suca≠b = s≤s (s≤s z≤n)
-- <-≠-suc {suc a} {zero} () suca≠b
-- <-≠-suc {suc zero} {suc zero} (s≤s ()) suca≠b
-- <-≠-suc {suc (suc a)} {suc zero} (s≤s ()) suca≠b
-- <-≠-suc {suc a} {suc (suc b)} (s≤s a<b) suca≠b = s≤s (<-≠-suc a<b (λ z → suca≠b (cong suc z)))


toℕ≤ : ∀ {a : ℕ} {fa : Fin (suc a)} -> (toℕ fa) ≤ a
toℕ≤ {zero} {zero} = z≤n
toℕ≤ {zero} {suc ()}
toℕ≤ {suc a} {zero} = z≤n
toℕ≤ {suc a} {suc fa} = s≤s toℕ≤


acc≤div-helper : ∀ {acc m a n} -> acc ≤ div-helper acc m a n
acc≤div-helper {acc} {m} {zero} {n} = ≤-refl refl
acc≤div-helper {acc} {m} {suc a} {zero} = start
  acc ≤⟨ ≤′⇒≤ (≤′-step ≤′-refl) ⟩
  suc acc ≤⟨ acc≤div-helper {suc acc} {m} {a} {m} ⟩
  div-helper (suc acc) m a m □
acc≤div-helper {acc} {m} {suc a} {suc n} = acc≤div-helper {acc} {m} {a} {n}

≤div-helper : ∀ {acc n a b m} -> a ≤ b -> div-helper acc n a m ≤ div-helper acc n b m
≤div-helper {acc} {n} {zero} {zero} z≤n = ≤-refl refl
≤div-helper {acc} {n} {zero} {suc b} {m} z≤n = acc≤div-helper {acc} {n} {suc b} {m}
≤div-helper {acc} {n} {suc a} {suc b} {zero} (s≤s a≤b) = ≤div-helper a≤b
≤div-helper {acc} {n} {suc a} {suc b} {suc m} (s≤s a≤b) = ≤div-helper a≤b

a*1≡a : ∀ {a} -> a * 1 ≡ a
a*1≡a {zero} = refl
a*1≡a {suc a} = cong suc a*1≡a


mod-helper≡0' : ∀ {acc a b} -> b ≤ a -> mod-helper acc a (suc b) b ≡ 0
mod-helper≡0' {acc} {zero} {zero} _ = refl
mod-helper≡0' {acc} {zero} {suc b} ()
mod-helper≡0' {acc} {suc a} {zero} b≤a = refl
mod-helper≡0' {acc} {suc a} {suc b} (s≤s b≤a) = mod-helper≡0' {suc acc} {suc a} {b} (≤-step b≤a)


mod-helper≡0'' : ∀ {k m b c} -> mod-helper k m (suc b + c) b ≡ mod-helper (b + k) m (2 + c) 1
mod-helper≡0'' {k} {m} {zero} {c} = refl
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
mod-helper≡0 {zero} {zero} = refl
mod-helper≡0 {zero} {suc c} = mod-helper≡0 {zero} {c}
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
*-inj {zero} {zero} {c} ()
*-inj {zero} {suc zero} {c} refl = refl
*-inj {zero} {suc (suc b)} {c} r rewrite m+0≡m {c} = ⊥-elim (≡-bot r)
  where
  ≡-bot : ∀{x y : ℕ} -> x ≡ x + (suc y) -> ⊥
  ≡-bot {zero} ()
  ≡-bot {suc x} {y} sx≡sx+y = ≡-bot {x} {y} (suc-inj sx≡sx+y)
*-inj {suc a} {zero} {c} ()
*-inj {suc a} {suc b} {c} r = cong suc (*-inj {a} {b} {c} (+-inj (suc c) r))


≡div : ∀ {a b} -> (a * (suc b)) div (suc b) ≡ a
≡div {zero} {b} = refl
≡div {suc a} {b} = sym lemma
  where
  lemma₁ : (suc a * suc b) ≡ ((suc a * suc b) div (suc b)) * (suc b)
  lemma₁ = begin
    (suc a * suc b) ≡⟨ property ((suc a * suc b) divMod (suc b)) ⟩
    toℕ ((suc a * suc b) mod (suc b)) + ((suc a * suc b) div (suc b)) * (suc b) ≡⟨ m+n≡m'+n' {toℕ (suc a * suc b mod suc b)} {0} (mod≡0 {a} {b}) refl ⟩
    ((suc a * suc b) div (suc b)) * (suc b) ∎

  lemma : suc a ≡ (suc a * suc b) div (suc b)
  lemma = *-inj lemma₁



_⊕_ : ∀ {k n : ℕ} -> Vec (Fin (suc n)) k -> Vec (Fin (suc n)) k -> (Vec (Fin (suc n)) k × Fin (suc n))
[] ⊕ [] = [] , zero
_⊕_ {n = n} (a ∷ xa) (b ∷ xb) =
  ( toℕ a + toℕ b + toℕ c ) mod (suc n) ∷ xa⊕xb ,
  fromℕ≤ {m = (toℕ a + toℕ b + toℕ c) div (suc n)} lemma
  where
  open Data.Nat.Properties.SemiringSolver

  xa⊕xb = proj₁ (xa ⊕ xb)
  c = proj₂ (xa ⊕ xb)

  lemma₁ : toℕ a + toℕ b + toℕ c ≤ 3 * n
  lemma₁ = start
    (toℕ a) + (toℕ b) + (toℕ c) ≤⟨ ≤-steps3 (toℕ a + toℕ b) (n + n) toℕ≤ (≤-steps3 (toℕ a) n toℕ≤ toℕ≤) ⟩
    n + n + n ≤⟨ ≤-refl (solve 1 (λ n -> n :+ n :+ n := con 3 :* n) refl n) ⟩
    3 * n □

  lemma₂₁ : ∀{n : ℕ} -> 3 * n ≤ 3 * (suc n)
  lemma₂₁ {n} = start
    3 * n ≤⟨ m≤m+n (3 * n) 3 ⟩
    3 * n + 3 ≤⟨ ≤-refl (solve 1 (λ n -> (con 3 :* n) :+ con 3 := con 3 :* (con 1 :+ n)) refl n) ⟩
    3 * (suc n) □

  lemma₂ : ∀ {n} -> (3 * n) div (suc n) < suc n
  lemma₂ {zero} = s≤s z≤n
  lemma₂ {suc zero} = s≤s lemma₂
  lemma₂ {suc (suc zero)} = s≤s lemma₂
  lemma₂ {suc (suc (suc n))} = start
    suc (3 * (3 + n) div (4 + n)) ≤⟨ s≤s (≤div-helper {0} {3 + n} {3 * (3 + n)} {3 * (4 + n)} {3 + n} (lemma₂₁ {3 + n})) ⟩
    suc (3 * (4 + n) div (4 + n)) ≤⟨ s≤s (≤-refl (≡div {3} {3 + n})) ⟩
    4 ≤⟨ s≤s (s≤s (s≤s (s≤s z≤n))) ⟩
    4 + n □

  lemma : (toℕ a + toℕ b + toℕ c) div (suc n) < suc n
  lemma = start
    suc ((toℕ a + toℕ b + toℕ c) div (suc n)) ≤⟨ s≤s (≤div-helper lemma₁) ⟩
    suc ((3 * n) div (suc n)) ≤⟨ lemma₂ ⟩
    suc n □
