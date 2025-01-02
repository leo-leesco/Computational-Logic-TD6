data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = m
succ n + m = succ (n + m)

infixl 6 _+_

_×_ : ℕ → ℕ → ℕ
zero × b = zero
succ a × b = (a × b) + b

infixl 7 _×_

data _≡_ {A : Set} (x : A) : (y : A) → Set where
  refl : x ≡ x

infix 4 _≡_

suc-≡ : {m n : ℕ} → (m ≡ n) → (succ m ≡ succ n)
suc-≡ refl = refl

+-unit-l : {n : ℕ} → zero + n ≡ n
+-unit-l = refl

+-unit-r : (n : ℕ) → n + zero ≡ n
+-unit-r zero = refl
+-unit-r (succ n) = suc-≡ (+-unit-r n)

+-assoc : (m n o : ℕ) → ((m + n) + o) ≡ (m + (n + o))
+-assoc zero n o = refl
+-assoc (succ m) n o = suc-≡ (+-assoc m n o)

+-succ : (m n : ℕ) → succ (m + n) ≡ m + succ n
+-succ zero n = refl
+-succ (succ m) n = suc-≡ (+-succ m n)

rec : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (succ n)) → (n : ℕ) → P n
rec P I H zero = I
rec P I H (succ n) = H n (rec P I H n)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- suc-≡ : {m n : ℕ} → (m ≡ n) → (succ m ≡ succ n)
-- suc-≡ = cong succ

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-unit-r n)
+-comm (succ m) n = trans (suc-≡ (+-comm m n)) (+-succ n m)

succ-inj : {m n : ℕ} → (succ m ≡ succ n) → m ≡ n
succ-inj refl = refl

open import Relation.Nullary
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

nat-dec : (m n : ℕ) → (m ≡ n) ∨ ¬ (m ≡ n)
nat-dec zero zero = left refl
nat-dec zero (succ n) = right (λ ())
nat-dec (succ m) zero = right (λ ())
nat-dec (succ m) (succ n) with nat-dec m n
... | left e = left (suc-≡ e)
... | right e = right (λ e' → e (succ-inj e'))

J : (A : Set) → (P : (x : A) → (y : A) → (p : x ≡ y) → Set) → (r : (x : A) → P x x refl) → (x : A) → (y : A) → (p : x ≡ y) → P x y p
J A P r x .x refl = r x


×-absorb-l : (m : ℕ) → zero × m ≡ zero
×-absorb-l m = refl

×-absorb-r : (m : ℕ) →  m × zero ≡ zero
×-absorb-r zero = refl
×-absorb-r (succ m) = trans (+-unit-r (m × zero)) (×-absorb-r m)

-- open ≡-Reasoning
begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

infix 1 begin_

_≡⟨_⟩_ : {A : Set} (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

infixr 2 _≡⟨_⟩_

_□ : {A : Set} (x : A) → x ≡ x
_□ _ = refl

infix 3 _□

×-succ : (m n : ℕ) → m × (succ n) ≡ m + (m × n)
×-succ zero n = refl
-- (m+1) (n+1) = m (n+1) + (n+1) [def]
-- = m + m n + n+1 [HR]
-- = (m + m n + n) + 1 [+-succ]
-- = (m+1) + n + m n [+-succ]
-- = (m+1) + m n + n [+-comm]
-- = (m+1) + (m+1)n [def]
×-succ (succ m) n = begin
  succ m × succ n ≡⟨ refl ⟩
  m × succ n + succ n ≡⟨ cong (λ { x → x + succ n }) (×-succ m n) ⟩
  (m + m × n) + succ n ≡⟨ sym (+-succ (m + m × n) n) ⟩
  succ(m + m × n + n) ≡⟨ cong succ (+-assoc m (m × n) n) ⟩
  succ(m + (m × n + n)) ≡⟨ refl ⟩
  succ m + (m × n + n) ≡⟨ cong (λ { x → succ m + x }) (sym refl) ⟩
  succ m + succ m × n □

dist-r : (m n o : ℕ) → (m + n) × o ≡ m × o + n × o
dist-r zero n o = refl
-- ((m+1) + n) × o ≡ (m + n + 1) × o
-- (m + n + 1) × o ≡ (m + n) × o + o
-- (m + n) × o + o ≡ (m × o) + (n × o) + o
-- (m × o) + (n × o) + o ≡ (m × o) + o + (n × o)
-- (m × o) + o + (n × o) ≡ ((m+1) × o) + (n × o)
dist-r (succ m) n o = begin
  (succ m + n) × o ≡⟨ refl ⟩
  succ(m + n) × o ≡⟨ refl ⟩
  (m + n) × o + o ≡⟨ cong (λ { x → x + o }) (dist-r m n o) ⟩
  m × o + n × o + o ≡⟨ +-assoc (m × o) (n × o) o ⟩
  m × o + (n × o + o) ≡⟨ cong (λ { x → m × o + x }) (+-comm (n × o) o) ⟩
  m × o + (o + n × o) ≡⟨ sym (+-assoc (m × o) o (n × o)) ⟩
  m × o + o + n × o ≡⟨ refl ⟩
  succ m × o + n × o □

×-comm : (m n : ℕ) → m × n ≡ n × m
×-comm zero n = trans (×-absorb-l n) (sym (×-absorb-r n))
-- (m+1) n
-- m n + n
-- n m + n
-- n + n m
-- n (m+1)
×-comm (succ m) n = begin
  succ m × n ≡⟨ refl ⟩
  m × n + n ≡⟨ cong (λ { x → x + n }) (×-comm m n) ⟩
  n × m + n ≡⟨ +-comm (n × m) n ⟩
  n + n × m ≡⟨ sym (×-succ n m) ⟩
  n × succ m □

×-assoc : (m n o : ℕ) → (m × n) × o ≡ m × (n × o)
×-assoc zero n o = refl
-- ((m+1) n) o
-- (m n + n) o
-- (m n) o + n o
-- m (n o) + n o
-- (m+1) (n o)
×-assoc (succ m) n o = begin 
  succ m × n × o ≡⟨ refl ⟩
  (m × n + n) × o ≡⟨ dist-r (m × n) n o ⟩
  (m × n) × o + n × o ≡⟨ cong (λ { x → x + n × o }) (×-assoc m n o) ⟩
  m × (n × o) + n × o ≡⟨ sym refl ⟩
  succ m × (n × o) □
