{-# OPTIONS --without-K #-}

module GibbonsCoPrograms where

-- code "scratchpad" Cartesian Seminar November 2021,
-- reading Gibbons : "How to design Co-Programs"

-------------------
-- natural numbers
-------------------

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

-- to enable use of natural number literals, e.g. "0", "1", "156372",...

{-# BUILTIN NATURAL ℕ #-} 

------------
-- Lists
------------

infixr 20 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

-------------
-- Booleans
-------------

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

-- boolean "less or equal" test on ℕ

infix 20 _≤?_

_≤?_ : ℕ → ℕ → 𝔹
Z ≤? m = true
S n ≤? Z = false
S n ≤? S m = n ≤? m

-------------------------
-- (type level) equality
-------------------------

infix 25 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  Refl : a ≡ a

-- (this is just to let Agda know about our definition
-- of equality, so in with clauses we can use "in eq")

{-# BUILTIN EQUALITY _≡_ #-}

-- i.e. for any type |A| and any two elements |a : A| and |b : A|,
-- we have defined the type |a ≡ b| (Note that within comments, we enclose
-- code snippets with |...|). The elements of this type are proofs that
-- |a| is equal to |b|. We have only one constructor, |Refl|.
-- It gives us, (for any type |A| and) for any |a : A|, a proof that |a| is
-- equal to itself. E.g. |1 ≡ 1| by |Refl|:

lala : (S Z) ≡ (S Z)
lala = Refl

-- This (|2 ≡ 1|) better should not typecheck (and it doesn't):
-- gugu : S (S Z) ≡ S Z
-- gugu = Refl

-- Ok, sounds rather boring so far... it will turn out that it isn't.

-- Here are some properties of equality, all proved by pattern matching
-- using the only constructor, |Refl|. That we are allowed to do this is
-- actually not completely trivial ... compare "path induction" in the
-- HoTT-book!

-- Reflexivity is just proved by |Refl| itself

≡-reflexive : {A : Set} → {a : A} → a ≡ a
≡-reflexive = Refl

-- We have Symmetry:

≡-symmetric : {A : Set} → {a b : A} → a ≡ b → b ≡ a
≡-symmetric Refl = Refl

-- and Transitivity:

≡-transitive : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-transitive Refl Refl = Refl

-- so, |≡| actually defines an equivalence relation on each type |A|.

-- We can introduce notation for equational reasoning:

_□ : {A : Set} → (a : A) → a ≡ a
a □ = Refl {a = a}

infixr 10 _≡⟨_⟩_

_≡⟨_⟩_ : {A : Set} → {b c : A} →
         (a : A) → a ≡ b → b ≡ c → a ≡ c
a ≡⟨ p ⟩ q = ≡-transitive p q

-- Here are two more interesting properties of |≡| :
-- it is a congruence with respect to an function, that means:

≡-cong : {A B : Set} → {a₁ a₂ : A} → (f : A → B) →
         a₁ ≡ a₂ → f a₁ ≡ f a₂
≡-cong f Refl = Refl

-- If |B| is a type family over a type |A| (e.g. |B a| is some
-- property of the element |a : A|), and |a₁ ≡ a₂|, there is
-- a map |B a₁ → B a₂| (e.g. from a proof that a₁ has property |B|,
-- one can deduce that a₂ also has property |B|):

≡-transport : {A : Set} → {B : A → Set} → {a₁ a₂ : A} →
              a₁ ≡ a₂ → B a₁ → B a₂
≡-transport Refl p = p


--------------------
-- insertion sort
--------------------

-- first for ℕ with ≤?

insertℕ : ℕ → List ℕ → List ℕ
insertℕ  n [] = n :: []
insertℕ  n (m :: ms) with n ≤? m        --  the "with" construct allows pattern matching
... | true  = n :: m :: ms              --  over the result of any expression, here |n ≤? m|.
... | false = m :: insertℕ  n ms        --  The dots (...) abbreviate |insertℕ n (m :: ms)| here.  

insertSortℕ : List ℕ → List ℕ
insertSortℕ  []        = []
insertSortℕ  (n :: ns) = insertℕ n (insertSortℕ ns)


testproof : insertSortℕ (3 :: 2 :: 1 :: []) ≡ (1 :: 2 :: 3 :: [])
-- We can prove this in equational reasoning style like
-- we did on the blackboard. Note that here the justifications
-- are just comments: all of them are definitions, and Agda knows
-- about these and uses them to do reduction. So the actual proof
-- for each step is just Refl.
testproof =
  insertSortℕ (3 :: 2 :: 1 :: [])
  ≡⟨ Refl {- Def insertSortℕ, rule #2 -} ⟩
  insertℕ 3 (insertSortℕ (2 :: 1 :: []))
  ≡⟨ Refl {- Def insertSortℕ, rule #2 -} ⟩
  insertℕ 3 (insertℕ 2 (insertSortℕ (1 :: [])))
  ≡⟨ Refl {- Def insertSortℕ, rule #2 -} ⟩
  insertℕ 3 (insertℕ 2 (insertℕ 1 (insertSortℕ [])))
  ≡⟨ Refl {- Def insertSortℕ, rule #1 -} ⟩
  insertℕ 3 (insertℕ 2 (insertℕ 1 []))
  ≡⟨ Refl {- Def insertℕ, rule #1 -} ⟩
  insertℕ 3 (insertℕ 2 (1 :: []))
  ≡⟨ Refl {- Def insertℕ, rule #2, case false -} ⟩
  insertℕ 3 (1 :: (insertℕ 2 []))
  ≡⟨ Refl {- Def insertℕ, rule #2, case false -} ⟩
  (1 :: insertℕ 3 (insertℕ 2 []))
  ≡⟨ Refl {- Def insertℕ, rule #1 -} ⟩
  (1 :: insertℕ 3 (2 :: []))
  ≡⟨ Refl {- Def insertℕ, rule #2, case false -} ⟩
  (1 :: 2 :: (insertℕ 3 []))
  ≡⟨ Refl {- Def insertℕ, rule #1 -} ⟩
  (1 :: 2 :: 3 :: [])
  □
-- And since
--   |≡-transitive Refl Refl = Refl|    (compare the definition of ≡-transitive)
-- we could also just write
-- |testproof = Refl|


-- insertSort can of course be formulated more generically:
-- the only additional ingredient we need is a boolean "less equal"
-- test for the type |A|, i.e. a function of type |A → A → 𝔹|:

insert : {A : Set} → (A → A → 𝔹) →
         A → List A → List A
insert le a [] = a :: []
insert le a (b :: bs) with le a b
...| true  = a :: b :: bs
...| false = b :: insert le a bs

insertSort : {A : Set} → ( A → A → 𝔹) →
             List A → List A
insertSort le  []       = []
insertSort le (a :: as) = insert le a (insertSort le as)

----------------------------------------- 
-- Properties of insertSort (and other
-- "sorting functions")
-----------------------------------------

-- For any type |A| and an arbitrary function of type |A → A → 𝔹| we have
-- defined a function
--  |insertSort {A} le : List A → List A|
-- Of course, if our "less equals" test doesn't have the properties we expect
-- from a "linear order", this function will not really deserve to be called
-- a "sorting": Think about what |insertSort {A} le| would do for |le| set to e.g.,
-- |λ x y → true|, |λ x y → false|, or (for |A = 𝔹|) |λ x y → x| 

-- So, we will define properties of functions |A → A → 𝔹| that are
-- reasonable to require of a "less equals" test:

-- Reflexivity: 

IsReflexive : {A : Set} → (A → A → 𝔹) → Set
IsReflexive {A} le = (a : A) → le a a ≡ true

-- Transitivity:

IsTransitive : {A : Set} → (A → A → 𝔹) → Set
IsTransitive {A} le = (a b c : A) → le a b ≡ true → le b c ≡ true → le a c ≡ true

-- Totality:

IsTotal : {A : Set} → (A → A → 𝔹) → Set
IsTotal {A} le = {a b : A} → le a b ≡ false → le b a ≡ true

-- Note that totality implies reflexivity:

IsTotal→IsReflexive : {A : Set} → (le : A → A → 𝔹) → IsTotal le → IsReflexive le
IsTotal→IsReflexive le tot a with le a a in eq   -- |eq| will be an equality
...| true  = Refl                                -- here, |eq : le a a ≡ true|
...| false =                                     -- here, |eq : le a a ≡ false|
        false
        ≡⟨ ≡-symmetric eq ⟩
        le a a
        ≡⟨ tot eq ⟩
        true
        □

-- Note that in the |le a a ≡ false| branch of this proof, the steps can not
-- just be replaced by Refl ! 


-----------------
-- Sorted lists
-----------------

-- Let's define the property of a list to be sorted w.r.t. some
-- "less equals"-Test |le : A → A → 𝔹| . That is, for any type
-- |A|, any function |le : A → A → 𝔹|, and any list |as : List A|,
-- we have to define a type whose elements are proofs that the list
-- |as| is sorted.

-- The idea is to define IsSorted inductively: the empty list is trivially
-- sorted, and a nonempty list is sorted when the tail is sorted and
-- the head is ... well, let's call this "ok to put before this tail":
-- If the tail is empty, every element is "ok to put before". Otherwise
-- the new element has to be less than the tails first element:

data OkAsHead {A : Set} (le : A → A → 𝔹 ) : A → List A → Set where
  OkAsHeadEmpty : (a : A) → OkAsHead le a []
  OkAsHeadNonEmpty : (a b : A) → (bs : List A) →
                     le a b ≡ true → OkAsHead le a (b :: bs)

data IsSorted {A : Set} (le : A → A → 𝔹) : List A → Set where
  IsSortedEmpty : IsSorted le []
  IsSortedNonEmpty : (a : A) → (bs : List A) →
                     OkAsHead le a bs → IsSorted le bs → IsSorted le (a :: bs)

-- We want to prove that |insertSort| produces sorted lists. The rough idea
-- is of course to do it by induction: the empty list is sorted, and if we
-- have a sorted list, inserting an element into it with |insert| (this is
-- what |insertSort| does), will yield a sorted list. So the heart of the
-- matter is to prove that |insert a bs| will be sorted whenever |bs| is
-- (this will be |insertSorted| below). As it turns out, it is useful to
-- first prove |okAsHeadLemma| which says that for elements |a b : A| and
-- a list |bs : List| such that |b| is ok as a head for |bs| and |le b a ≡ true|,
-- |b| will also be ok as a head for |insert a bs| ... after all, the head of
-- |insert a bs| is either |a| or the head of |bs|. 

okAsHeadLemma : {A : Set} → (le : A → A → 𝔹) → 
                (a b : A) → (bs : List A) → OkAsHead le b bs → le b a ≡ true  →
                OkAsHead le b (insert le a bs)
okAsHeadLemma le a b [] bOk leba = OkAsHeadNonEmpty b a [] leba
okAsHeadLemma le a b (b' :: bs') bOk leba with le a b'
... | true  = OkAsHeadNonEmpty b a (b' :: bs') leba
... | false with bOk
...   | (OkAsHeadNonEmpty _ _ _ lebb') = OkAsHeadNonEmpty b b' (insert le a bs') lebb'

-- Now we can prove |insertSorted|. Note the use of |tot|, the totality assumption
-- on |le|: in the case where the argument list is nonempty, i.e. matches the pattern
-- |b :: bs|, and |le a b ≡ false| (witnessed by |eq|), we need |tot| to get a proof
-- of |le b a ≡ true| that we can use in the call to |okAsHeadLemma|.

insertSorted : {A : Set} → (le : A → A → 𝔹 ) → IsTotal le →
               (a : A) → (bs : List A) →
               IsSorted le bs → IsSorted le (insert le a bs)
insertSorted le tot a [] IsSortedEmpty = IsSortedNonEmpty a [] (OkAsHeadEmpty a) IsSortedEmpty
insertSorted le tot a (b :: bs) (IsSortedNonEmpty b bs bOk bsSorted) with le a b in eq
... | true  = let
                okAsHeadabbs : OkAsHead le a (b :: bs)
                okAsHeadabbs = OkAsHeadNonEmpty a b bs eq
                bbsSorted : IsSorted le (b :: bs)
                bbsSorted = (IsSortedNonEmpty b bs bOk bsSorted)
              in
                IsSortedNonEmpty a (b :: bs) okAsHeadabbs bbsSorted
... | false = let
                bOkinsabs : OkAsHead le b (insert le a bs)
                bOkinsabs = okAsHeadLemma le a b bs bOk (tot eq)
                insabsSorted : IsSorted le (insert le a bs)
                insabsSorted = insertSorted le tot a bs bsSorted
              in
                IsSortedNonEmpty b (insert le a bs) bOkinsabs insabsSorted

-- As we hoped, insertSortSorted now is a simple induction on the input list:

insertSortSorted : {A : Set} → (le : A → A → 𝔹) → IsTotal le →
                (as : List A) → IsSorted le (insertSort le as)
insertSortSorted le tot [] = IsSortedEmpty
insertSortSorted le tot (a :: as) = 
              let
                asSorted = insertSort le as
                IH : IsSorted le (insertSort le as)
                IH = insertSortSorted le tot as
              in
                insertSorted le tot a asSorted IH

