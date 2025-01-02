data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

_∧_ : Bool → Bool → Bool
true ∧ true = true
true ∧ false = false
false ∧ true = false
false ∧ false = false


_∨_ : Bool → Bool → Bool
true ∨ true = true
true ∨ false = true
false ∨ true = true
false ∨ false = false

data _≡_ {A : Set} (x : A) : (y : A) → Set where
  refl : x ≡ x

infix 4 _≡_

not-inv : (b : Bool) → not (not b) ≡ b
not-inv true = refl
not-inv false = refl

conj-not : (b : Bool) → (not b) ∧ b ≡ false
conj-not true = refl
conj-not false = refl
