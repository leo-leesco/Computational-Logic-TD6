open import Data.List

-- hd : {A : Set} → List A → A : impossible because nothing guarantees that List A has at least one element

open import Data.Nat

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

vec-hd : {A : Set} {n : ℕ} → Vec A (suc n) → A
vec-hd (x ∷ l) = x

vec-tl : {A : Set} {n : ℕ} → Vec A (suc n) → A
vec-tl (x ∷ []) = x
vec-tl (x ∷ (y ∷ l)) = vec-tl (y ∷ l)

vec-concat : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
vec-concat [] l2 = l2
vec-concat (x ∷ l1) l2 = x ∷ vec-concat l1 l2

vec-append : {A : Set} {n : ℕ} → Vec A n → A → Vec A (suc n)
vec-append [] x = x ∷ []
vec-append (y ∷ l) x = y ∷ vec-append l x

vec-rev : {A : Set} {n : ℕ} → Vec A n → Vec A n
vec-rev [] = []
vec-rev (x ∷ l) = vec-append l x

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

vec-ith : {A : Set} → {n : ℕ} → Fin n → Vec A n → A
vec-ith zero (x ∷ l) = x
vec-ith (suc i) (x ∷ l) = vec-ith i l

open import Data.Product hiding (zip)

vec-zip : {A : Set} {n : ℕ} → Vec A n → Vec A n → Vec (A × A) n
vec-zip [] [] = []
vec-zip (x ∷ l1) (y ∷ l2) = (x , y) ∷ vec-zip l1 l2
