open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

open import Data.Nat

length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ l) = length l + 1

concat : {A : Set} → List A → List A → List A
concat [] l = l
concat (x ∷ l1) l2 = x ∷ concat l1 l2

concat-length : {A : Set} → List A → List A → ℕ
concat-length l1 l2 = length l1 + length l2

concat-assoc : {A : Set} → (l1 l2 l3 : List A) → concat (concat l1 l2) l3 ≡ concat l1 (concat l2 l3)
concat-assoc [] l2 l3 = refl
concat-assoc (x ∷ l1) l2 l3 = cong (λ l → x ∷ l) (concat-assoc l1 l2 l3)

append : {A : Set} → List A → A → List A
append [] x = x ∷ []
append (y ∷ l) x = y ∷ (append l x)

rev : {A : Set} → List A → List A
rev [] = []
rev (x ∷ l) = append (rev l) x

length-append : {A : Set} → (l : List A) → (x : A) → length (append l x) ≡ length l + 1
length-append [] x = refl
length-append (y ∷ l) x = begin
  length (append (y ∷ l) x) ≡⟨ refl ⟩
  length (y ∷ (append l x)) ≡⟨ refl ⟩
  length (append l x) + 1 ≡⟨ cong (λ { k → k + 1 }) (length-append l x) ⟩
  length l + 1 + 1 ≡⟨ refl ⟩
  length (y ∷ l) + 1 ∎

rev-length : {A : Set} → (l : List A) → length (rev l) ≡ length l
rev-length [] = refl
-- #(x+l).rev
-- # l.rev + [x]
-- # l.rev + 1
rev-length (x ∷ l) = begin
  length (rev(x ∷ l)) ≡⟨ refl ⟩
  length (append (rev l) x) ≡⟨ length-append (rev l) x ⟩
  length (rev l) + 1 ≡⟨ cong (λ { k → k + 1 }) (rev-length l) ⟩
  length l + 1  ≡⟨ refl ⟩
  length (x ∷ l) ∎

rev-append : {A : Set} → (l : List A) → (x : A) → rev (append l x) ≡ x ∷ (rev l)
rev-append [] x = refl
rev-append (y ∷ l) x = cong (λ l → append l y) (rev-append l x)

rev-rev : {A : Set} → (l : List A) → rev (rev l) ≡ l
rev-rev [] = refl
rev-rev (x ∷ l) = trans (rev-append (rev l) x) (cong (λ l → x ∷ l) (rev-rev l))

open import Data.Bool

filter : {A : Set} → (p : A → Bool) → (l : List A) → List A
filter p [] = []
filter p (x ∷ l) with p x
... | true = x ∷ filter p l
... | false = filter p l

filter-false : {A : Set} → (l : List A) → filter (λ x → false) l ≡ []
filter-false [] = refl
filter-false (x ∷ l) = filter-false l

filter-true : {A : Set} → (l : List A) → filter (λ x → true) l ≡ l
filter-true [] = refl
filter-true (x ∷ l) = cong (λ l' → x ∷ l') (filter-true l)
