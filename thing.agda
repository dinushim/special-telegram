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

assoc-helper : (y z : ℕ) → suc (y + suc z) ≡ suc y + suc z
assoc-helper = λ y z → refl

assoc-helper-R : (y z : ℕ) → suc y + suc z ≡ suc (y + suc z)
assoc-helper-R = λ y z → refl

assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
assoc zero y z = refl
assoc (suc x) zero zero = zero-idL (suc x + (zero + zero))
assoc (suc x) zero (suc z) rewrite zero-idL x = refl
assoc (suc x) (suc y) zero rewrite zero-idL y = cong suc (zero-idL (x + suc y))
assoc (suc x) (suc y) (suc z) rewrite assoc-helper y z = cong suc (assoc x (suc y) (suc z))

cong-add : (x y z : ℕ) → y ≡ z → x + y ≡ x + z
cong-add zero zero zero = λ _ → refl
cong-add zero y z = λ z₁ → z₁
cong-add (suc x) zero zero = λ _ → refl
cong-add (suc x) zero (suc z) = λ ()
cong-add (suc x) (suc y) zero = λ ()
cong-add (suc x) (suc y) (suc z) prf rewrite prf = refl

assoc2 : (x y z : ℕ) → x + y + z ≡ x + (y + z)
assoc2 zero y z = refl
assoc2 (suc x) zero zero = cong suc (zero-idL (x + zero))
assoc2 (suc x) zero (suc z) rewrite zero-idL x = refl
assoc2 (suc x) (suc y) zero rewrite zero-idL y = cong suc (zero-idL (x + suc y))
assoc2 (suc x) (suc y) (suc z) rewrite assoc-helper-R y z = cong suc (assoc2 x (suc y) (suc z))

zero-inside : (x y : ℕ) → x + y ≡ x + 0 + y
zero-inside zero zero = refl
zero-inside zero (suc y) = refl
zero-inside (suc x) zero = cong suc (zero-inside x zero)
zero-inside (suc x) (suc y) = cong suc (zero-inside x (suc y))

assoc2-R : (x y z : ℕ) → x + (y + z) ≡ x + y + z
assoc2-R zero zero zero = refl
assoc2-R zero zero (suc z) = refl
assoc2-R zero (suc y) zero = refl
assoc2-R zero (suc y) (suc z) = refl
assoc2-R (suc x) zero zero rewrite zero-idL x = cong suc (zero-idR x)
assoc2-R (suc x) zero (suc z) = cong suc (zero-inside x (suc z))
assoc2-R (suc x) (suc y) zero rewrite zero-idL y = cong suc (zero-idR (x + suc y))
assoc2-R (suc x) (suc y) (suc z) = cong suc (assoc2-R x (suc y) (suc z))

helperception : (x y z : ℕ) → (L : List ℕ) → x + (y + fold2 _+_ 0 L + suc z) ≡
      x + (y + fold2 _+_ 0 L) + suc z
helperception zero y z L = refl
helperception (suc x) y z L = cong suc (helperception x y z L)

insert-sum-helper : (x elt : ℕ) → (L : List ℕ) → x + (fold-sum L + elt) ≡ fold-sum (x ∷ L) + elt
insert-sum-helper zero elt L = refl
insert-sum-helper (suc x) zero [] rewrite zero-idL x = cong suc (zero-idR x)
insert-sum-helper (suc x) zero (x₁ ∷ L) rewrite zero-idL (x₁ + fold2 _+_ 0 L) = cong suc (zero-idR (x + (x₁ + fold2 _+_ zero L)))
insert-sum-helper (suc x) (suc elt) [] rewrite zero-idL x = refl
insert-sum-helper (suc x) (suc elt) (x₁ ∷ L) = cong suc (helperception x x₁ elt L)

insert-sum : (pos elt : ℕ) → (L : List ℕ) → fold-sum (insert pos elt L) ≡ fold-sum L + elt
insert-sum pos elt [] = zero-idL elt
insert-sum zero elt (x ∷ L) = add-comm elt (x + fold2 _+_ zero L)
insert-sum (suc pos) elt (x ∷ L) =
  trans (cong (λ z → x + z) (insert-sum pos elt L)) (insert-sum-helper x elt L)

remove-and-shift : (x : List ℕ) → (a : ℕ) → List ℕ --- needs to be redone, or a modified apply function needs to be written
remove-and-shift [] a = []
remove-and-shift (x ∷ x₁) zero = x₁
remove-and-shift (x ∷ x₁) (suc a) = remove-and-shift x₁ a



adjust : {n : ℕ} → (h : Fin (suc n) → Fin (suc n)) → Fin n → Fin n
adjust h x  with h Fin.zero | {!!} _≤?_ {!!} --????????
... | a | b = {! !} 

perm-adjust : {n : ℕ} →  (g : Permutation (suc n) (suc n)) → (Permutation n n)
perm-adjust (perm f f-inv left right) = perm (adjust f) {!!} {!!} {!!} 


{-

with f g Fin.zero | f-inv g Fin.zero
consider [1,2,3,4,5] and [4,2,3,1,5]. we should be insering 1 into position 3 to the list that results from applying the same permutation to the list obtained by deleting 
the one. however, this would put 2 in position zero, which means that 2 will then get shifted to position 3

this should give [3,4,2,5] into which we insert 1 into position 3, giving [3,4,2,1,5], which is not what we wanted (but I don't quite know how to write this in agda)
-}

length2 : (L : List ℕ) → ℕ
length2 L = suc (mylength L)

want-helper : (x : ℕ) → (L : List ℕ)
            → let L' = x ∷ L in
               (g : Permutation (mylength L') (mylength L'))
            → apply L' g ≡
                    insert (Data.Fin.toℕ (f g Data.Fin.zero)) x
                    (remove-and-shift (apply L' g)
                    (Data.Fin.toℕ (f-inv g Data.Fin.zero)))
want-helper x [] g with f g Fin.zero | f-inv g Fin.zero
... | Fin.zero | Fin.zero = refl
... | Fin.zero | Fin.suc ()
... | Fin.suc () | _
want-helper x (y ∷ L) g with f g Fin.zero | f-inv g Fin.zero
... | Fin.zero | Fin.zero = refl
... | Fin.zero | Fin.suc m = {!!} --- if f(0) = 0, f-inv(0) should be zero
... | Fin.suc n | Fin.zero = {!!} -- if f-inv(0) = 0, f(0) should be zero, not suc (a)
... | Fin.suc n | Fin.suc m = {!!}

{-want-helper : (x : List ℕ) → (g : Permutation (mylength x) (mylength x))
              → (apply x g) ≡
                       insert (Data.Fin.toℕ (f g {!Data.Fin.zero!})) (head x)
                       (remove-and-shift (apply x g) (Data.Fin.toℕ (f-inv g {!Data.Fin.zero!})))
want-helper [] (perm f f-inv left right) = {!!}
want-helper (x ∷ x₁) (perm f f-inv left right) = {!!}

-}
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
