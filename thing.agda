module thing (A : Set) where

open import Data.Bool hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Nat
open import Data.Fin using (Fin)
open import Data.Vec using (toList; fromList; tabulate; lookup)
open import Data.Maybe

eqtest : ℕ -> ℕ -> Bool
eqtest x y = ⌊ x ≟ y ⌋

elt-of : List ℕ → ℕ → Bool
elt-of [] x = false
elt-of (x ∷ a) b = eqtest x b ∨ elt-of a b

mylength : List ℕ → ℕ
mylength l = foldr (λ _ → suc) 0 l

counter : List ℕ → ℕ → ℕ
counter [] a = 0
counter (x ∷ x₁) a =
        if  ⌊ x ≟ a ⌋ then suc (counter x₁ a)
        else counter x₁ a

fold2 : (ℕ → ℕ → ℕ) → ℕ → List ℕ → ℕ
fold2 _ c [] = c
fold2 f c (x ∷ xs) = f x (fold2 f c xs)

max2 : ℕ → ℕ → ℕ
max2 a b with a ≤? b
max2 a b | yes p = b
max2 a b | no ¬p = a

max : (x : List ℕ) → ℕ
max l = fold2 max2 0 l

fold-sum : (x : List ℕ) → ℕ
fold-sum = fold2 _+_ 0

sum-helper : 0 ≡ fold-sum []
sum-helper = refl

record Permutation (n m : ℕ) : Set where
  constructor perm
  field
    f : Fin n → Fin m
    f-inv : Fin m → Fin n
    left : (x : Fin n) → f-inv (f x) ≡ x
    right : (x : Fin m) → f (f-inv x) ≡ x

open Permutation

apply : (l : List ℕ) → Permutation (mylength l) (mylength l) → List ℕ
apply [] p = []
apply (x ∷ l) p = toList (tabulate (λ i → lookup (f p i) (fromList (x ∷ l))))

want : (x : List ℕ) → (g : Permutation (mylength x) (mylength x)) → fold-sum x ≡ fold-sum (apply x g)
want [] g = refl
want (x ∷ x₁) g = {!!}

insert : (pos elt : ℕ) → (L : List ℕ) → List ℕ
insert _ elt [] = elt ∷ []
insert zero elt (x ∷ L) = elt ∷ x ∷ L
insert (suc pos) elt (x ∷ L) = x ∷ insert pos elt L

zero-idL : (x : ℕ) → x + 0 ≡ x
zero-idL zero = refl
zero-idL (suc x) rewrite zero-idL x = refl

fold-zero : (L : List ℕ) → fold-sum (zero ∷ L) ≡ fold-sum L
fold-zero L = refl

zero-idR : (x : ℕ) → x ≡ x + 0
zero-idR zero = refl
zero-idR (suc x) = cong suc (zero-idR x)

obvious : (x : ℕ) → (L : List ℕ) → x ∷ L ≡ insert 0 x L
obvious x [] = refl
obvious x (x₁ ∷ L) = refl

shift-suc : (x y : ℕ) → suc (x + y) ≡ x + suc y
shift-suc zero y = refl
shift-suc (suc x) y = cong suc (shift-suc x y)

add-comm : (x y : ℕ) → x + y ≡ y + x
add-comm zero zero = refl
add-comm zero (suc y) = cong suc (zero-idR y)
add-comm (suc x) y = trans (cong suc (add-comm x y)) (shift-suc y x)

insert-sum : (pos elt : ℕ) → (L : List ℕ) → fold-sum (insert pos elt L) ≡ fold-sum L + elt
insert-sum pos elt [] = zero-idL elt
insert-sum zero elt (x ∷ L) = add-comm elt (x + fold2 _+_ zero L)
insert-sum (suc pos) elt (x ∷ L) =
  trans (cong (λ z → x + z) (insert-sum pos elt L)) {!!} -- by associativity

-- No, this is very bad.  Instead, create a list with known head (for want-helper).
head : (L : List ℕ) → ℕ  --not entirely accurate but should be okay? be careful (Maybe/just makes issues?)
head [] = 0
head (x ∷ L) = x

remove-and-shift : (x : List ℕ) → (a b : ℕ) → List ℕ
remove-and-shift = {!!}

want-helper : (x : List ℕ) → (g : Permutation (mylength x) (mylength x)) → (apply x g) ≡ insert {! f 0!} (head x) (remove-and-shift {!!} {!!} {!!})
want-helper [] (perm f f-inv left right) = {!!}
want-helper (x ∷ x₁) (perm f f-inv left right) = {!!}


{-
1) fold-sum(insert (r, k) , L) = fold-sum L + k
2) g(l1, ... , ln) = insert l1, sigma(0), g'(l2, ... , ln)
3) use ind-hyp to get fold-sum(g(l2, ... , ln) = foldsum (l2, ...., ln)
4) combine 1 and 3 to get result

-}

summer : (x : List ℕ) → (lim : ℕ) → ℕ
summer [] lim = 0
summer (x ∷ x₁) zero = 0
summer (x ∷ x₁) (suc lim) = ((suc lim) * counter (x ∷ x₁) (suc lim)) + summer (x ∷ x₁) lim

counterlemma : (x : List ℕ) → fold-sum x ≡ summer x (max x) -- sum 0 (max x) mult( n, counter x n)
counterlemma [] = refl
counterlemma (x ∷ x₁) = {!!}

{-

obtaining a list of one element shorter from a permutation of Sn+1 by fixing the first element:

[a b c] -> [b c a] i.e. (132)
need to obtain permutation on two elements by fixing first



---
miniproof : (x : List ℕ) → (g : Permutation) → (a : ℕ) → counter x a ≡ counter (f g x)  a
miniproof [] (perm f length-pres count-pres) a = count-pres [] a
miniproof (x ∷ x₁) (perm f length-pres count-pres) a = count-pres (x ∷ x₁) a

postulate helper1 : (g : Permutation) → f g [] ≡ []

prooftrial1 : (g : Permutation) → f g [] ≡ []
prooftrial1 (perm f length-pres count-pres) = {!!}
-- proof by length maintenance lengthpres implies length f [] = length [] = 0, helper2 implies f [] is then empty

Proof1 : (x : List ℕ) → (g : Permutation) → fold-sum x ≡ fold-sum (f g x)
Proof1 [] g rewrite helper1 g = refl
Proof1 (x ∷ x₁) g = {!!} -- cong {!!} (Proof1 x₁ g)
-- collection of summands - fold-sum of L is equal to n1 1 + n2 2 + n3 3, count-pres forces these ni to be maintained, which gives the result

--settingup large sums:

counterlemma : (x : List ℕ) → fold-sum x ≡ {!!} -- sum 0 (max x) mult( n, counter x n)
counterlemma = {!!}
-}
