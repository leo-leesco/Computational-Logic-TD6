module Div2 where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Nat
open import Data.Nat.Properties -- using (+-suc ; *-identityˡ)
open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

div2 : ℕ → ℕ
div2 0 = 0
div2 (suc 0) = 0
div2 (suc (suc x)) = suc (div2 x)

test5 : ℕ
test5 = div2 (suc (suc (suc (suc (suc 0))))) -- 2

*-2 : (n : ℕ) → 2 * n ≡ n + n
*-2 n = begin
  2 * n ≡⟨ refl ⟩
  n + 1 * n ≡⟨ cong (λ { x → n + x }) (*-identityˡ n) ⟩
  n + n ∎

data Even : ℕ → Set where
  even-0 : Even 0
  even-suc : {n : ℕ} → Even n → Even (suc (suc n))

div2-correct : (n : ℕ) → 2 * div2 n ≡ n ∨ suc (2 * div2 n) ≡ n
div2-correct 0 = left refl
div2-correct 1 = right refl
div2-correct (suc (suc n)) with div2-correct n
... | left even = left (begin
  2 * div2 (suc (suc n)) ≡⟨ refl ⟩
  2 * suc (div2 n) ≡⟨ *-2 (suc (div2 n)) ⟩
  suc (div2 n) + suc (div2 n) ≡⟨ +-suc (suc (div2 n)) (div2 n) ⟩
  suc (suc (div2 n) + div2 n) ≡⟨ cong suc (+-comm (suc (div2 n)) (div2 n)) ⟩
  suc (div2 n + suc (div2 n)) ≡⟨ cong suc (+-suc (div2 n) (div2 n)) ⟩
  suc (suc(div2 n + div2 n)) ≡⟨ cong (λ { x → suc (suc x) }) (sym (*-2 (div2 n))) ⟩
  suc (suc(2 * div2 n)) ≡⟨ cong (λ { x → suc (suc x) }) even ⟩
  suc (suc n) ∎)
... | right odd = right (begin
  suc (2 * div2 (suc (suc n))) ≡⟨ refl ⟩
  suc (2 * suc (div2 n)) ≡⟨ cong suc (*-2 (suc (div2 n))) ⟩
  suc (suc (div2 n) + suc (div2 n)) ≡⟨ cong suc (+-suc (suc (div2 n)) (div2 n)) ⟩
  suc (suc (suc (div2 n) + div2 n)) ≡⟨ cong (λ { x → suc (suc x) }) (+-comm (suc (div2 n)) (div2 n)) ⟩
  suc (suc (div2 n + suc (div2 n))) ≡⟨ cong (λ { x → suc (suc x) }) (+-suc (div2 n) (div2 n)) ⟩
  suc (suc (suc(div2 n + div2 n))) ≡⟨ cong (λ { x → suc (suc (suc x)) }) (sym (*-2 (div2 n))) ⟩
  suc (suc (suc(2 * div2 n))) ≡⟨ cong (λ { x → suc (suc x) }) odd ⟩
  suc (suc n) ∎)

open import Data.Product

div2' : (n : ℕ) → Σ ℕ (λ q → (2 * q ≡ n) ∨ (suc (2 * q) ≡ n))
div2' zero = zero , left refl
div2' 1 = zero , right refl
div2' (suc (suc n)) with div2' n
... | q , left 2*q≡n = suc q , left (begin
  2 * (suc q) ≡⟨ *-comm 2 (suc q) ⟩
  (suc q) * 2 ≡⟨ refl ⟩
  2 + q * 2  ≡⟨ cong (λ { x → 2 + x }) (*-comm q 2) ⟩
  2 + 2 * q  ≡⟨ cong (λ { x → 2 + x }) 2*q≡n ⟩
  2 + n  ≡⟨ refl ⟩
  suc(1 + n)  ≡⟨ refl ⟩
  suc (suc (0 + n))  ≡⟨ cong (λ { x → suc (suc x) }) refl ⟩
  suc (suc n) ∎)
... | q , right 2*q+1≡n = suc q , right (begin
  suc (2 * suc q) ≡⟨ cong suc (*-comm 2 (suc q)) ⟩
  suc (suc q * 2) ≡⟨ cong suc refl ⟩
  suc (2 + q * 2)  ≡⟨ cong (λ { x → suc (2 + x) }) (*-comm q 2) ⟩
  suc (2 + 2 * q) ≡⟨ sym (+-suc 2 (2 * q)) ⟩
  2 + suc (2 * q) ≡⟨ cong (λ { x → 2 + x }) 2*q+1≡n ⟩
  2 + n ≡⟨ refl ⟩
  suc(1 + n)  ≡⟨ refl ⟩
  suc (suc (0 + n))  ≡⟨ cong (λ { x → suc (suc x) }) refl ⟩
  suc (suc n) ∎)
