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

open import NatProps
open import IntProps




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
  lemma₂ {0} = s≤s z≤n
  lemma₂ {1} = s≤s lemma₂
  lemma₂ {2} = s≤s lemma₂
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
