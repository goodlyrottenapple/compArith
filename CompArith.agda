module CompArith where

-- open import Data.Empty
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Nat
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple

open import Data.Integer as Int using (ℤ; +_; sign; _⊖_) renaming (_*_ to _ℤ*_; _+_ to _ℤ+_; _-_ to _ℤ-_; _≤_ to _ℤ≤_)

open import Data.Vec
open import Data.Sign using (Sign)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning
-- open import Relation.Nullary using (¬_; Dec; yes; no)

open import Algebra
import Data.Integer.Properties as IntegerProp
private
  module CRℤ = CommutativeRing IntegerProp.commutativeRing

open import NatProps
open import IntProps

𝔹 = Fin 2

-- ∥_∥ : 𝔹 -> ℕ
-- ∥ zero ∥ = 0
-- ∥ suc zero ∥ = 1
-- ∥ suc (suc ()) ∥
-- ∥ 1 ∥ = 1

-- compl : ∀ {k} -> Vec 𝔹 (ℕ.suc k) -> Vec 𝔹 (ℕ.suc k)
-- compl {zero} (x ∷ []) = not x ∷ []
-- compl {suc k} (x ∷ xs) = not x ∷ compl xs

Σ : ∀ {k} -> Vec 𝔹 k -> ℕ
Σ {zero} [] = 0
Σ {suc i} (zero ∷ xs) = Σ xs
Σ {suc i} (suc zero ∷ xs) = (2 ^ i) + Σ xs
Σ {suc i} (suc (suc ()) ∷ xs)


Σspec : ∀ {k} -> Vec 𝔹 k -> ℕ
Σspec {0} [] = 0
Σspec {suc i} (x ∷ xs) = toℕ x * 2 ^ i + Σ xs


-- Σ is a better def. to work with ... similar to the def. of ⟪_⟫
Σspec≡Σ : ∀ {k} (x : Vec 𝔹 k) -> Σspec x ≡ Σ x
Σspec≡Σ [] = refl
Σspec≡Σ (zero ∷ xs) = refl
Σspec≡Σ {suc i} (suc zero ∷ xs) rewrite 1*m≡m {2 ^ i} = refl
Σspec≡Σ {suc i} (suc (suc ()) ∷ xs)


⟦_⟧ : ∀ {k} -> Vec 𝔹 (ℕ.suc k) -> ℤ
⟦ xs ⟧ = + Σ xs


⟪_⟫ : ∀ {k} -> Vec 𝔹 (ℕ.suc k) -> ℤ
⟪_⟫ {k} (zero ∷ xs) = + Σ xs
⟪_⟫ {k} (suc zero ∷ xs) = - (2 ^ k) ℤ+ (+ Σ xs)
⟪_⟫ {k} (suc (suc ()) ∷ xs)


σ : ∀ {k} -> Vec 𝔹 (ℕ.suc k) -> Sign
σ (zero ∷ xs) = Sign.+
σ (suc zero ∷ xs) = Sign.-
σ (suc (suc ()) ∷ xs)


Top : ∀ {k : ℕ} -> Vec 𝔹 k
Top {zero} = []
Top {suc k} = suc zero ∷ Top


≤-Top : ∀ {k} {x : Vec 𝔹 k} -> Σ x ≤ Σ (Top {k})
≤-Top {zero} {[]} = z≤n
≤-Top {suc k} {zero ∷ xs} = ≤-steps {Σ xs} {Σ {k} Top} (2 ^ k) (≤-Top {k})
≤-Top {suc k} {suc zero ∷ xs} = ≤-steps2 (2 ^ k) (≤-Top {k})
≤-Top {suc k} {suc (suc ()) ∷ xs}


lem1-1-1 : ∀ {k} -> Σ (Top {k}) ≡ (2 ^ k) ∸ 1 -- equiv to ⟦ Top {k} ⟧ ≡ (2 ^ k) ∸ 1
lem1-1-1 {zero} = refl
lem1-1-1 {suc k} rewrite lem1-1-1 {k} | +-right-identity (2 ^ k) = begin
  (2 ^ k) + ((2 ^ k) ∸ 1) ≡⟨ sym (+-∸-assoc (2 ^ k) {2 ^ k} {1} (1≤2^k {k})) ⟩ refl


lem1-1 : ∀ {k} {x : Vec 𝔹 (suc k)} -> sign ⟪ x ⟫ ≡ σ x
lem1-1 {k} {zero ∷ xs} = refl
lem1-1 {k} {suc zero ∷ xs} = aux₂ (- (2 ^ k) ℤ+ + Σ xs) aux
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

  aux : ⟪ suc zero ∷ xs ⟫ ℤ≤ - 1
  aux rewrite sym aux₁ | sym (lem1-1-1 {k}) = ℤ≤-steps (- (2 ^ k)) (Int.+≤+ (≤-Top {k}))

lem1-1 {k} {suc (suc ()) ∷ xs}


_mod𝔹 : ℕ -> 𝔹
0 mod𝔹 = zero
1 mod𝔹 = suc zero
suc (suc a) mod𝔹 = a mod𝔹


_div𝔹 : ℕ -> 𝔹
0 div𝔹 = zero
1 div𝔹 = zero
suc (suc a) div𝔹 = suc zero


div𝔹spec : ∀ {a b c : 𝔹} -> toℕ ( ( (toℕ a) + (toℕ b) + (toℕ c) ) div𝔹 ) ≡ ⌊ (toℕ a) + (toℕ b) + (toℕ c) /2⌋
div𝔹spec {zero} {zero} {zero} = refl
div𝔹spec {zero} {zero} {suc zero} = refl
div𝔹spec {zero} {zero} {suc (suc ())}
div𝔹spec {zero} {suc zero} {zero} = refl
div𝔹spec {zero} {suc zero} {suc zero} = refl
div𝔹spec {zero} {suc zero} {suc (suc ())}
div𝔹spec {zero} {suc (suc ())}
div𝔹spec {suc zero} {zero} {zero} = refl
div𝔹spec {suc zero} {zero} {suc zero} = refl
div𝔹spec {suc zero} {zero} {suc (suc ())}
div𝔹spec {suc zero} {suc zero} {zero} = refl
div𝔹spec {suc zero} {suc zero} {suc zero} = refl
div𝔹spec {suc zero} {suc zero} {suc (suc ())}
div𝔹spec {suc zero} {suc (suc ())}
div𝔹spec {suc (suc ())}


-- addition

_⊕_ : ∀ {k : ℕ} -> Vec 𝔹 k -> Vec 𝔹 k -> (Vec 𝔹 k × 𝔹)
[] ⊕ [] = [] , zero
(a ∷ xa) ⊕ (b ∷ xb) =
  ( ( (toℕ a) + (toℕ b) + (toℕ c) ) mod𝔹 ) ∷ xa⊕xb , ( (toℕ a) + (toℕ b) + (toℕ c) ) div𝔹
  where
  xa⊕xb = proj₁ (xa ⊕ xb)
  c = proj₂ (xa ⊕ xb)


_←!_ : ∀ {a} {A : Set a} m {n} -> Vec A (m + suc n) -> A
0 ←! (x ∷ _) = x
(suc m) ←! (_ ∷ xs) = m ←! xs

si+k≡i+sk : ∀ {i k} -> suc i + k ≡ i + suc k
si+k≡i+sk {zero} {k} = refl
si+k≡i+sk {suc i} = cong suc (si+k≡i+sk {i})

∁ : ∀ {k : ℕ} (i : ℕ) -> Vec 𝔹 (i + suc k) -> Vec 𝔹 (i + suc k) -> 𝔹
∁ 0 a b = zero
∁ {k} (suc i) a b rewrite si+k≡i+sk {i} {suc k} = ( (toℕ (i ←! a) ) + (toℕ (i ←! b) ) + (toℕ (∁ i a b) ) ) div𝔹


r : ∀ {k : ℕ} (i : ℕ) -> Vec 𝔹 (i + suc k) -> Vec 𝔹 (i + suc k) -> 𝔹
r i a b = ( (toℕ (i ←! a) ) + (toℕ (i ←! b) ) + (toℕ (∁ i a b) ) ) mod𝔹



--
-- -- keep : ∀ {a} {A : Set a} {m} n → Vec A (m + n) → Vec A n
-- -- keep {m = m} n = drop m {n = n}
-- --
-- drop-0 : ∀ {a} {A : Set a} {k : ℕ} {v : Vec A (k + 0)} -> drop k v ≡ []
-- drop-0 {k = k} {v} with splitAt k v
-- drop-0 {v = .(ys ++ [])} | ys , [] , refl = refl
--
-- lem2-1-1 : ∀ {k : ℕ} (i : ℕ) (a b : Vec 𝔹 (suc k + i)) ->
--   drop (suc k) (proj₁ (a ⊕ b)) ≡ proj₁ ((drop (suc k) a) ⊕ (drop (suc k) b))
-- lem2-1-1 {k} 0 a b rewrite
--   drop-0 {k = suc k} {proj₁ (a ⊕ b)} |
--   drop-0 {k = suc k} {a} |
--   drop-0 {k = suc k} {b} = refl
-- lem2-1-1 {k} (suc i) a b = {!   !}

-- lem2-1-1 : ∀ {k : ℕ} (i : ℕ) (a b : Vec 𝔹 (suc k + i)) ->
--   keep {m = suc k} i (proj₁ (a ⊕ b)) ≡ proj₁ ((keep {m = suc k} i a) ⊕ (keep {m = suc k} i b))
-- lem2-1-1 {k} 0 a b rewrite
--   keep-0 {k = suc k} {proj₁ (a ⊕ b)} |
--   keep-0 {k = suc k} {a} |
--   keep-0 {k = suc k} {b} = refl
-- lem2-1-1 {k} (suc i) a b = {! a  !}
  -- where
  -- ih : keep {m = suc (suc )} i (proj₁ (a ⊕ b)) ≡ proj₁ (keep {m = suc (suc k)} i a ⊕ keep  {m = suc (suc k)} i b)
  -- ih = lem2-1-1 i ? ?

--
-- lem2-1 : ∀ {k i : ℕ} (a b : Vec 𝔹 (i + suc k)) -> proj₁ ((false ∷ (drop i a)) ⊕ (false ∷ (drop i a))) ≡ false ∷ drop i (proj₁ (a ⊕ b)) -- (proj₂ (a ⊕ a)) ∷ (proj₁ (a ⊕ a))
-- lem2-1 = {!   !}
