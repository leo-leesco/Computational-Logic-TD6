open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open import Div2

open ≡-Reasoning

div2-double : (n : ℕ) → div2 (2 * n) ≡ n
div2-double 0 = refl
div2-double (suc n) = begin
  div2 (2 * (suc n)) ≡⟨ cong div2 (*-2 (suc n)) ⟩
  div2 ((suc n) + (suc n)) ≡⟨ cong div2 (+-suc (suc n) n) ⟩
  div2 (suc (suc n + n)) ≡⟨ cong (λ { x → div2 (suc x) }) (+-comm (suc n) n) ⟩
  div2 (suc (n + suc n)) ≡⟨ cong (λ { x → div2 (suc x) }) (+-suc n n)  ⟩
  div2 (suc (suc (n + n))) ≡⟨ cong (λ { x → div2 (suc (suc x)) }) (sym (*-2 n)) ⟩
  div2 (suc (suc (2 * n))) ≡⟨ refl ⟩
  suc(div2(2 * n)) ≡⟨ cong suc (div2-double n) ⟩
  suc n ∎

triangular : ℕ → ℕ
triangular 0 = 0
triangular (suc n) = triangular n + suc n

triang3 : ℕ
triang3 = triangular 3

lem-gauss : (n : ℕ) → 2 * triangular n ≡ n * suc n
lem-gauss 0 = refl
lem-gauss (suc n) = begin
  2 * triangular (suc n) ≡⟨ refl ⟩
  2 * (triangular n + suc n) ≡⟨ *-distribˡ-+ 2 (triangular n) (suc n) ⟩
  2 * triangular n + 2 * suc n ≡⟨ cong (λ { x → x + 2 * suc n }) (lem-gauss n) ⟩
  n * suc n + 2 * suc n  ≡⟨ sym (*-distribʳ-+ (suc n) n 2) ⟩
  (n + 2) * suc n ≡⟨ cong (λ { x → x * suc n }) (+-comm n 2) ⟩
  (2 + n) * suc n ≡⟨ cong (λ { x → x * suc n }) (+-suc 1 n) ⟩
  (suc (1 + n)) * suc n ≡⟨ cong (λ { x → (suc x) * suc n }) (+-suc 0 n) ⟩
  (suc (suc (0 + n))) * suc n ≡⟨ cong (λ { x → suc (suc x) * suc n }) (+-identityˡ n) ⟩
  suc (suc n) * suc n ≡⟨ *-comm (suc (suc n)) (suc n) ⟩
  suc n * suc (suc n) ∎

gauss : (n : ℕ) → triangular n ≡ div2 (n * suc n)
gauss n = begin
  triangular n ≡⟨ sym (div2-double (triangular n)) ⟩
  div2 (2 * triangular n) ≡⟨ cong div2 (lem-gauss n) ⟩
  div2 (n * suc n) ∎
