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
open Int.≤-Reasoning
  renaming (begin_ to startℤ_; _∎ to _ℤ□; _≡⟨_⟩_ to _≡ℤ⟨_⟩_; _≤⟨_⟩_ to _ℤ≤⟨_⟩_)
  
open import Data.Vec
open import Data.Sign using (Sign)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning
-- open import Relation.Nullary using (¬_; Dec; yes; no)

open import Algebra
import Data.Integer.Properties as IntegerProp
private
  module CR = CommutativeRing IntegerProp.commutativeRing

private
  module CS = CommutativeSemiring Data.Nat.Properties.commutativeSemiring


open import NatProps
open import IntProps

𝔹 = Fin 2

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
Σspec {suc i} (x ∷ xs) = toℕ x * 2 ^ i + Σspec xs

Σspec-step : ∀ {k} -> Vec 𝔹 k -> ℕ
Σspec-step  {0} [] = 0
Σspec-step {suc i} (x ∷ xs) = toℕ x * 2 ^ i + Σ xs


-- Σ is a better def. to work with ... similar to the def. of ⟪_⟫
Σspec≡Σ : ∀ {k} (x : Vec 𝔹 k) -> Σspec x ≡ Σ x
Σspec≡Σ [] = refl
Σspec≡Σ (zero ∷ xs) = Σspec≡Σ xs
Σspec≡Σ {suc i} (suc zero ∷ xs) rewrite 1*m≡m {2 ^ i} = cong (_+_ (2 ^ i)) (Σspec≡Σ xs)
Σspec≡Σ {suc i} (suc (suc ()) ∷ xs)


Σspec-step≡Σ : ∀ {k} (x : Vec 𝔹 k) -> Σspec-step x ≡ Σ x
Σspec-step≡Σ [] = refl
Σspec-step≡Σ (zero ∷ xs) = refl
Σspec-step≡Σ {suc i} (suc zero ∷ xs) rewrite 1*m≡m {2 ^ i} = refl
Σspec-step≡Σ {suc i} (suc (suc ()) ∷ xs)


⟦_⟧ : ∀ {k} -> Vec 𝔹 (ℕ.suc k) -> ℕ
⟦ xs ⟧ = Σ xs


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

Bot : ∀ {k : ℕ} -> Vec 𝔹 k
Bot {zero} = []
Bot {suc k} = zero ∷ Bot


≤-Top : ∀ {k} {x : Vec 𝔹 k} -> Σ x ≤ Σ (Top {k})
≤-Top {zero} {[]} = z≤n
≤-Top {suc k} {zero ∷ xs} = ≤-steps {Σ xs} {Σ {k} Top} (2 ^ k) (≤-Top {k})
≤-Top {suc k} {suc zero ∷ xs} = ≤-steps2 (2 ^ k) (≤-Top {k})
≤-Top {suc k} {suc (suc ()) ∷ xs}


ΣBot≡0 : ∀ {k} -> Σ (Bot {k}) ≡ 0
ΣBot≡0 {zero} = refl
ΣBot≡0 {suc k} = ΣBot≡0 {k}

Bot-≤ : ∀ {k} {x : Vec 𝔹 k} -> Σ (Bot {k}) ≤ Σ x
Bot-≤ {k} {x} rewrite ΣBot≡0 {k} = z≤n


lem-1-1-aux1 : ∀ {k} -> Σ (Top {k}) ≡ (2 ^ k) ∸ 1 -- equiv to ⟦ Top {k} ⟧ ≡ (2 ^ k) ∸ 1
lem-1-1-aux1 {zero} = refl
lem-1-1-aux1 {suc k} rewrite lem-1-1-aux1 {k} | +-right-identity (2 ^ k) = begin
  (2 ^ k) + ((2 ^ k) ∸ 1) ≡⟨ sym (+-∸-assoc (2 ^ k) {2 ^ k} {1} (1≤2^k {k})) ⟩ refl


lem-1-1 : ∀ {k} {x : Vec 𝔹 (suc k)} -> sign ⟪ x ⟫ ≡ σ x
lem-1-1 {k} {zero ∷ xs} = refl
lem-1-1 {k} {suc zero ∷ xs} = aux₂ (- (2 ^ k) ℤ+ + Σ xs) aux
  where
  aux₁ : - (2 ^ k) ℤ+ + ((2 ^ k) ∸ 1) ≡ - 1
  aux₁ = begin
    - (2 ^ k) ℤ+ + ((2 ^ k) ∸ 1) ≡⟨ cong (_ℤ+_ (- (2 ^ k))) (sym (⊖-≥ (1≤2^k {k}))) ⟩
    - (2 ^ k) ℤ+ ((2 ^ k) ⊖ 1) ≡⟨ cong (_ℤ+_ (- (2 ^ k))) (m⊖n≡mℤ-n (2 ^ k) 1) ⟩
    - (2 ^ k) ℤ+ (+ (2 ^ k) ℤ+ - 1) ≡⟨ sym (CR.+-assoc (- (2 ^ k)) (+ (2 ^ k)) (- 1)) ⟩
    (- (2 ^ k) ℤ+ + (2 ^ k)) ℤ+ - 1 ≡⟨ CR.+-comm (- (2 ^ k) ℤ+ + (2 ^ k)) (- 1) ⟩
    - 1 ℤ+ (- (2 ^ k) ℤ+ + (2 ^ k)) ≡⟨ cong (_ℤ+_ (- 1)) (CR.+-comm (- (2 ^ k)) (+ (2 ^ k))) ⟩
    - 1 ℤ+ (+ (2 ^ k) ℤ- + (2 ^ k)) ≡⟨ cong (_ℤ+_ (- 1)) (sym (m⊖n≡mℤ-n (2 ^ k) (2 ^ k))) ⟩
    - 1 ℤ+ ((2 ^ k) ⊖ (2 ^ k)) ≡⟨ cong (_ℤ+_ (- 1)) (IntegerProp.n⊖n≡0 (2 ^ k)) ⟩
    - 1 ∎

  aux₂ : ∀ x -> x ℤ≤ - 1 -> sign x ≡ Sign.-
  aux₂ (+_ n) ()
  aux₂ (Int.-[1+_] n) x≤ℤ-1 = refl

  aux : ⟪ suc zero ∷ xs ⟫ ℤ≤ - 1
  aux rewrite sym aux₁ | sym (lem-1-1-aux1 {k}) = ℤ≤-steps (- (2 ^ k)) (Int.+≤+ (≤-Top {k}))

lem-1-1 {k} {suc (suc ()) ∷ xs}


_mod𝔹 : ℕ -> 𝔹
0 mod𝔹 = zero
1 mod𝔹 = suc zero
suc (suc a) mod𝔹 = a mod𝔹

mod𝔹spec : ∀ {a} -> toℕ ( a mod𝔹 ) ≡ a mod 2
mod𝔹spec {zero} = refl
mod𝔹spec {suc zero} = refl
mod𝔹spec {suc (suc a)} = mod𝔹spec {a}


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


-- _←!_ : ∀ {a} {A : Set a} m {n} -> Vec A (m + suc n) -> A
-- 0 ←! (x ∷ _) = x
-- (suc m) ←! (_ ∷ xs) = m ←! xs


-- si+k≡i+sk : ∀ {i k} -> suc i + k ≡ i + suc k
-- si+k≡i+sk {zero} {k} = refl
-- si+k≡i+sk {suc i} = cong suc (si+k≡i+sk {i})


-- ∁ : ∀ {k : ℕ} (i : ℕ) -> Vec 𝔹 (i + suc k) -> Vec 𝔹 (i + suc k) -> 𝔹
-- ∁ 0 a b = zero
-- ∁ {k} (suc i) a b rewrite si+k≡i+sk {i} {suc k} = ( (toℕ (i ←! a) ) + (toℕ (i ←! b) ) + (toℕ (∁ i a b) ) ) div𝔹


-- r : ∀ {k : ℕ} (i : ℕ) -> Vec 𝔹 (i + suc k) -> Vec 𝔹 (i + suc k) -> 𝔹
-- r i a b = ( (toℕ (i ←! a) ) + (toℕ (i ←! b) ) + (toℕ (∁ i a b) ) ) mod𝔹

-- lem-2-2-aux1 : ∀ {k : ℕ} {a b : 𝔹} {xa xb : Vec 𝔹 k} -> ⟦ a ∷ xa ⟧ + ⟦ b ∷ xb ⟧ ≡ ⟦ xa ⟧ + ⟦ xb ⟧ + toℕ a * (2 ^ k) + toℕ b * (2 ^ k)
-- lem-2-2-aux1 = ?


lem-2-2-aux1 : ∀ {a b c : 𝔹} -> toℕ a + toℕ b + toℕ c ≡ toℕ ((toℕ a + toℕ b + toℕ c) div𝔹) * 2 + toℕ ((toℕ a + toℕ b + toℕ c) mod𝔹)
lem-2-2-aux1 {zero} {zero} {zero} = refl
lem-2-2-aux1 {zero} {zero} {suc zero} = refl
lem-2-2-aux1 {zero} {zero} {suc (suc ())}
lem-2-2-aux1 {zero} {suc zero} {zero} = refl
lem-2-2-aux1 {zero} {suc zero} {suc zero} = refl
lem-2-2-aux1 {zero} {suc zero} {suc (suc ())}
lem-2-2-aux1 {zero} {suc (suc ())}
lem-2-2-aux1 {suc zero} {zero} {zero} = refl
lem-2-2-aux1 {suc zero} {zero} {suc zero} = refl
lem-2-2-aux1 {suc zero} {zero} {suc (suc ())}
lem-2-2-aux1 {suc zero} {suc zero} {zero} = refl
lem-2-2-aux1 {suc zero} {suc zero} {suc zero} = refl
lem-2-2-aux1 {suc zero} {suc zero} {suc (suc ())}
lem-2-2-aux1 {suc zero} {suc (suc ())}
lem-2-2-aux1 {suc (suc ())}


lem-2-2 : ∀ {k : ℕ} {a b : Vec 𝔹 (suc k)} -> ⟦ a ⟧ + ⟦ b ⟧ ≡ ⟦ proj₂ (a ⊕ b) ∷ proj₁ (a ⊕ b) ⟧
lem-2-2 {zero} {zero ∷ []} {zero ∷ []} = refl
lem-2-2 {zero} {zero ∷ []} {suc zero ∷ []} = refl
lem-2-2 {zero} {zero ∷ []} {suc (suc ()) ∷ []}
lem-2-2 {zero} {suc zero ∷ []} {zero ∷ []} = refl
lem-2-2 {zero} {suc zero ∷ []} {suc zero ∷ []} = refl
lem-2-2 {zero} {suc zero ∷ []} {suc (suc ()) ∷ []}
lem-2-2 {zero} {suc (suc ()) ∷ []} {b ∷ []}
lem-2-2 {suc k} {a ∷ xa} {b ∷ xb} rewrite
  sym (Σspec-step≡Σ {suc (suc k)} (a ∷ xa)) | sym (Σspec-step≡Σ {suc (suc k)} (b ∷ xb)) |
  sym (Σspec-step≡Σ {suc (suc (suc k))} (((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) div𝔹) ∷ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) mod𝔹) ∷ proj₁ (xa ⊕ xb))) |
  sym (Σspec-step≡Σ {suc (suc k)} (((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) mod𝔹) ∷ proj₁ (xa ⊕ xb))) |
  m+0≡m {2 ^ k} | m+0≡m {(2 ^ k) + (2 ^ k)} = begin
    toℕ a * ((2 ^ k) + (2 ^ k)) + ⟦ xa ⟧ + (toℕ b * ((2 ^ k) + (2 ^ k)) + ⟦ xb ⟧) ≡⟨ a+b+c+d≡a+c+b+d {toℕ a * ((2 ^ k) + (2 ^ k))} ⟩
    toℕ a * ((2 ^ k) + (2 ^ k)) + toℕ b * ((2 ^ k) + (2 ^ k)) + (⟦ xa ⟧ + ⟦ xb ⟧) ≡⟨ cong (_+_ (toℕ a * ((2 ^ k) + (2 ^ k)) + toℕ b * ((2 ^ k) + (2 ^ k)))) ih ⟩
    toℕ a * ((2 ^ k) + (2 ^ k)) + toℕ b * ((2 ^ k) + (2 ^ k)) + (toℕ (proj₂ (xa ⊕ xb)) * ((2 ^ k) + (2 ^ k)) + ⟦ proj₁ (xa ⊕ xb) ⟧)
      ≡⟨ sym (CS.+-assoc (toℕ a * ((2 ^ k) + (2 ^ k)) + toℕ b * ((2 ^ k) + (2 ^ k))) (toℕ (proj₂ (xa ⊕ xb)) * ((2 ^ k) + (2 ^ k))) ⟦ proj₁ (xa ⊕ xb) ⟧) ⟩
    toℕ a * ((2 ^ k) + (2 ^ k)) + toℕ b * ((2 ^ k) + (2 ^ k)) + toℕ (proj₂ (xa ⊕ xb)) * ((2 ^ k) + (2 ^ k)) + ⟦ proj₁ (xa ⊕ xb) ⟧ ≡⟨ a*x+b*x+c*x+d≡x*a+b+c+d {(2 ^ k) + (2 ^ k)} {toℕ a} {toℕ b} ⟩
    ((2 ^ k) + (2 ^ k)) * ( toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb)) ) + ⟦ proj₁ (xa ⊕ xb) ⟧
      ≡⟨ m+n≡m'+n' {((2 ^ k) + (2 ^ k)) * ( toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb)) )} {m' = ((2 ^ k) + (2 ^ k)) * ( toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) div𝔹) * 2 + toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) mod𝔹) )}
        (cong (_*_ ((2 ^ k) + (2 ^ k))) (lem-2-2-aux1 {a} {b} {proj₂ (xa ⊕ xb)}))
        refl ⟩
    ((2 ^ k) + (2 ^ k)) * ( toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) div𝔹) * 2 + toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) mod𝔹) ) + ⟦ proj₁ (xa ⊕ xb) ⟧
      ≡⟨ x*a*x+b+c≡a*x+b*x+x+c {(2 ^ k) + (2 ^ k)} {toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) div𝔹)} ⟩
    toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) div𝔹) * ((2 ^ k) + (2 ^ k) + ((2 ^ k) + (2 ^ k))) + toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) mod𝔹) * ((2 ^ k) + (2 ^ k)) + ⟦ proj₁ (xa ⊕ xb) ⟧
      ≡⟨ CS.+-assoc (toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) div𝔹) * ((2 ^ k) + (2 ^ k) + ((2 ^ k) + (2 ^ k)))) (toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) mod𝔹) * ((2 ^ k) + (2 ^ k))) ⟦ proj₁ (xa ⊕ xb) ⟧ ⟩
    toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) div𝔹) * ((2 ^ k) + (2 ^ k) + ((2 ^ k) + (2 ^ k))) + (toℕ ((toℕ a + toℕ b + toℕ (proj₂ (xa ⊕ xb))) mod𝔹) * ((2 ^ k) + (2 ^ k)) + ⟦ proj₁ (xa ⊕ xb) ⟧)  ∎
  where
  ih : ⟦ xa ⟧ + ⟦ xb ⟧ ≡ toℕ (proj₂ (xa ⊕ xb)) * ((2 ^ k) + (2 ^ k)) + ⟦ proj₁ (xa ⊕ xb) ⟧
  ih rewrite 2^k+2^k≡2^sk {k} | Σspec-step≡Σ {suc (suc k)} (proj₂ (xa ⊕ xb) ∷ proj₁ (xa ⊕ xb))= lem-2-2 {k} {xa} {xb}

  a+b+c+d≡a+c+b+d : ∀ {a b c d : ℕ} -> a + b + (c + d) ≡ a + c + (b + d)
  a+b+c+d≡a+c+b+d {a} {b} {c} {d} = solve 4 (λ a b c d -> a :+ b :+ (c :+ d) := a :+ c :+ (b :+ d)) refl a b c d
    where
    open Data.Nat.Properties.SemiringSolver

  a*x+b*x+c*x+d≡x*a+b+c+d : ∀ {x a b c d : ℕ} -> a * x + b * x + c * x + d ≡ x * (a + b + c) + d
  a*x+b*x+c*x+d≡x*a+b+c+d {x} {a} {b} {c} {d} = solve 5 (λ x a b c d -> a :* x :+ b :* x :+ c :* x :+ d := x :* (a :+ b :+ c) :+ d) refl x a b c d
    where
    open Data.Nat.Properties.SemiringSolver

  x*a*x+b+c≡a*x+b*x+x+c : ∀ {x a b c : ℕ} -> x * (a * 2 + b) + c ≡ a * (x + x) + b * x + c
  x*a*x+b+c≡a*x+b*x+x+c {x} {a} {b} {c} = solve 4 (λ x a b c -> x :* (a :* con 2 :+ b) :+ c := a :* (x :+ x) :+ b :* x :+ c) refl x a b c
    where
    open Data.Nat.Properties.SemiringSolver


-- lemma 2.4

⟪Top⟫ : ∀ {k : ℕ} -> Vec 𝔹 k
⟪Top⟫ {zero} = []
⟪Top⟫ {suc k} = zero ∷ Top


⟪Bot⟫ : ∀ {k : ℕ} -> Vec 𝔹 k
⟪Bot⟫ {zero} = []
⟪Bot⟫ {suc k} = suc zero ∷ Bot



≤-⟪Top⟫ : ∀ {k} {x : Vec 𝔹 (suc k)} -> ⟪ x ⟫ ℤ≤ ⟪ ⟪Top⟫ {suc k} ⟫
≤-⟪Top⟫ {k} {zero ∷ xs} = Int.+≤+ (≤-Top {k})
≤-⟪Top⟫ {k} {suc zero ∷ xs} = startℤ
  (- (2 ^ k)) ℤ+ + Σ xs ℤ≤⟨ ℤ≤-steps (- (2 ^ k)) ( Int.+≤+ (≤-Top {k}) ) ⟩
  (- (2 ^ k)) ℤ+ + Σ (Top {k}) ℤ≤⟨ -k+mℤ≤m (2 ^ k) ⟩
  ⟪ ⟪Top⟫ {suc k} ⟫ ℤ□
≤-⟪Top⟫ {k} {suc (suc ()) ∷ xs}


⟪Bot⟫-≤ : ∀ {k} {x : Vec 𝔹 (suc k)} -> ⟪ ⟪Bot⟫ {suc k} ⟫ ℤ≤ ⟪ x ⟫
⟪Bot⟫-≤ {k} {zero ∷ xs} rewrite ΣBot≡0 {k} | CR.+-comm (- (2 ^ k)) (+ 0) | (proj₁ CR.+-identity) (- (2 ^ k)) = startℤ
  - (2 ^ k) ℤ≤⟨ -≤0 (2 ^ k) ⟩ + 0 ℤ≤⟨ Int.+≤+ z≤n ⟩ + Σ xs ℤ□ 
⟪Bot⟫-≤ {k} {suc zero ∷ xs} rewrite ΣBot≡0 {k} = ℤ≤-steps (- (2 ^ k)) (Int.+≤+ z≤n)
⟪Bot⟫-≤ {x = suc (suc ()) ∷ xs}
