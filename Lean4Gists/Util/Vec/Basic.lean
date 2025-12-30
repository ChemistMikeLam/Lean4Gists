/-
Copyright (c) 2025 ChemistMikeLam. All rights reserved.
Released under GNU General Public License version 3.0 or later.
See file LICENSE for a copy of the license.

Authors:
- ChemistMikeLam <43129403+ChemistMikeLam at users dot noreply dot github dot com>
-/

module

/-!
# Length-indexed vectors

This file only contains defintions of datatype and functions.
Lemmas are put into `Lean4Gists.Util.Vec.Lemma`.

Because the vector type have the length encoded in the type, it could be unwieldy to manipulate at times.
In particular, casts might be needed to covince the compiler that the vector have the length expected by the type.

Many functions in this file create new vector(s) by manipulating input vector(s).
These new vectors commonly have lengths that are somehow related to the input vector length.
This file provides two variants for these functions.
One of them, with a suffix `'` in their name, returns proofs of such relation, alongside with the resultant vector(s).
These proofs could be useful for theorem proving, but have a more verbose return type.
The other variant have no suffix `'` in their name.
They are basically abbreviations of the corresponding with-proof variant function, but stripped of the proof.
This might make it more useful in normal programming, for the simpler return types.
-/

namespace Lean4Gists.Util

/--
Length-indexed vectors.
-/
public inductive Vec.{u} (α : Type u) : Nat → Type u

  /--
  An empty vector.
  -/
  | public nil : Vec α 0

  /--
  A nonempty vector consists of a head element and a tail vector.
  -/
  | public cons {n : Nat} (h : α) (t : Vec α n) : Vec α n.succ

namespace Vec

/-!
### Derived instances
-/

deriving instance
    Repr
  , BEq
  , ReflBEq
  , LawfulBEq
  , DecidableEq
  , Hashable
for Vec

/-!
### Conversion to and from `List`
-/

/--
Convert a list into a vector.
The length of the vector should be the same as the length of the input list.
`O(n)`.
-/
public def _root_.List.toVec.{u} {α : Type u} : List α → (n : Nat) × Vec α n
  | [] => ⟨0, nil⟩
  | x :: xs =>
    let ⟨n, vxs⟩ := xs.toVec
    ⟨n + 1, cons x vxs⟩

/--
Convert a vector to a list.
The length information is lost in the type.
Still, the resultant list should have the same length as the input vector.
`O(n)`.
-/
public def toList.{u} {α : Type u} {n : Nat} : Vec α n → List α
  | nil => []
  | cons x xs => x :: xs.toList

/-!
### Constructing a vector from a seed
-/

/--
Wraps a value in a singleton vector.
`O(1)`.
-/
@[expose]
public abbrev singleton.{u} {α : Type u} (a : α) : Vec α 1 :=
  cons a nil

/--
Generate a vector of length `n` from an element-generating function and a seed.
`O(n)`.
-/
public def unfold_n.{u, v} {α : Type u} {β : Type v} (f : α → α × β) (seed : α) : (n : Nat) → Vec β n
  | 0 => nil
  | i + 1 =>
    let (newSeed, elem) := f seed
    cons elem $ unfold_n f newSeed i

/--
Generate a vector of length `n` where all elements are `a`.
`O(n)`.
-/
@[expose]
public abbrev ofRepeat.{u} {α : Type u} (a : α) (n : Nat) : Vec α n :=
  unfold_n (λ a => (a, a)) a n

/-!
### `Inhabited` and `Nonempty` instances
-/

/--
There is always an empty vector.
-/
public instance {α : Type u} : Inhabited (Vec α 0) where
  default := nil

/--
If the element type is inhabited, then the nonempty vector types are inhabited.

Uses `ofRepeat` to avoid instance search depth problems.
-/
public instance {α : Type u} {n : Nat} [insta : Inhabited α] : Inhabited (Vec α n.succ) where
  default := ofRepeat insta.default n.succ

/--
The type of dependent pair, where the first element is the length of the vector in the second element, is inhabited.
-/
public instance {α : Type u} : Inhabited ((n : Nat) × Vec α n) where
  default := ⟨default, by simpa using default⟩

/--
There is always an empty vector.
-/
public instance {α : Type u} : Nonempty (Vec α 0) :=
  inferInstance

/--
If the element type is nonempty, then the nonempty vector types are nonempty.

Uses `ofRepeat` to avoid instance search depth problems.
-/
public instance {α : Type u} {n : Nat} [insta : Nonempty α] : Nonempty (Vec α n.succ) := by
  obtain ⟨a⟩ := insta
  exact ⟨ofRepeat a n.succ⟩

/--
The type of dependent pair, where the first element is the length of the vector in the second element, is nonempty.
-/
public instance {α : Type u} : Nonempty ((n : Nat) × Vec α n) :=
  inferInstance

/-!
### Possibly non-terminating vector generation
-/

/--
Generate a list from an element-generating function and a seed.
Terminates when `f` returns `none`;
if `f` always return `some` this function will not terminate.
-/
public partial def unfold.{u, v} {α : Type u} {β : Type v} (f : α → Option (α × β)) (seed : α) : (n : Nat) × Vec β n :=
  match f seed with
  | none => ⟨0, nil⟩
  | some (newSeed, elem) =>
    let ⟨n, v⟩ := unfold f newSeed
    ⟨n.succ, cons elem v⟩

/-!
### `Ord`, `LT`, `LE`, `Max` and `Min` instances
-/

/--
Imposes a dictionary order on the two vectors.
Takes time linear to length of shared prefix.
-/
public def compare.{u} {α : Type u} [Ord α] {m n : Nat} : Vec α m → Vec α n → Ordering
  | nil, nil => .eq
  | nil, cons _ _ => .lt
  | cons _ _, nil => .gt
  | cons a as, cons b bs => (Ord.compare a b).then (compare as bs)

/-!
The following instances and notations only work between vectors of same length.
-/

/--
Vectors have an ordering if the elemtents have an ordering.
-/
public instance {α : Type u} [Ord α] {n : Nat} : Ord (Vec α n) where
  compare := compare

/--
Allow use of `<` notation.
-/
public instance {α : Type u} [Ord α] {n : Nat} : LT (Vec α n) :=
  ltOfOrd

/--
`<` of vectors are decidable.
-/
public instance {α : Type u} [Ord α] {n : Nat} : DecidableLT (Vec α n) :=
  inferInstance

/--
Allow use of `≤` notation.
-/
public instance {α : Type u} [Ord α] {n : Nat} : LE (Vec α n) :=
  leOfOrd

/--
`≤` of vectors are decidable.
-/
public instance {α : Type u} [Ord α] {n : Nat} : DecidableLE (Vec α n) :=
  inferInstance

/--
Allow use of `Max.max`.
-/
public instance {α : Type u} [Ord α] {n : Nat} : Max (Vec α n) :=
  maxOfLe

/--
Allow use of `Min.min`.
-/
public instance {α : Type u} [Ord α] {n : Nat} : Min (Vec α n) :=
  minOfLe

/-!
### `Functor` interface
-/

/--
Standard `Functor` `map`, but allow map across universes.
`O(n)`.
-/
public def map.{u, v} {α : Type u} {β : Type v} {n : Nat} (f : α → β) : Vec α n → Vec β n
  | nil => nil
  | cons a t => cons (f a) $ t.map f

/--
Vectors are functors.
-/
public instance {n : Nat} : Functor (Vec · n) where
  map := map

/-!
### Vector length, emptiness and in-bounds checks
-/

/--
Length of the vector, which is in the type.
`O(1)`.
-/
@[expose]
public abbrev length.{u} {α : Type u} {n : Nat} : Vec α n → Nat
  | _ => n

/--
An abbreviation for emptiness prop.
`O(1)`.
-/
@[expose]
public abbrev emptyProp.{u} {α : Type u} {n : Nat} : Vec α n → Prop
  | _ => n = 0

/--
The emptiness prop is decidable.
-/
public instance {α : Type u} {n : Nat} : @DecidablePred (Vec α n) emptyProp :=
  inferInstance

/--
Emptiness check returning `Bool`.
`O(1)`.
-/
@[expose]
public abbrev isEmpty.{u} {α : Type u} {n : Nat} (v : Vec α n) : Bool :=
  decide v.emptyProp

/--
An abbreviation for in-bounds prop.
`O(1)`.
-/
@[expose]
public abbrev inBounds.{u} {α : Type u} {n : Nat} : Vec α n → Nat → Prop
  | _ => (· < n)

/--
The in-bounds prop is decidable.
-/
public instance {α : Type u} {n : Nat} : @DecidableRel (Vec α n) Nat inBounds :=
  inferInstance

/--
In-bounds check returning `Bool`.
`O(1)`.
-/
@[expose]
public abbrev isInBounds.{u} {α : Type u} {n : Nat} (v : Vec α n) (i : Nat) : Bool :=
  decide (v.inBounds i)

/-!
### `GetElem` interface

These functions do not enforce that vector length not be 0 in the type.
However, because you have to construct a proof that the index is less than the length,
and there being no way to construct the proof if the vector has zero length,
they effectively only allow indexing into nonempty vectors.
(With the exception of `v[i]!`, which does not require any proof, and would panic when you use it on an empty vector.)
-/

/--
Gets the `i`th element of the vector.
Requires proof that the index is in bounds.
`O(i)`.
-/
public def getElem.{u} {α : Type u} {n : Nat} (v : Vec α n) (i : Nat) (h : inBounds v i) : α :=
  match i, v with
  | 0, cons a _ => a
  | j + 1, cons _ as => getElem as j (by simpa using h)

/--
Similar to `getElem`, but use `Fin n`, which carries the needed proof.
`O(i)`.
-/
public abbrev getElemFin.{u} {α : Type u} {n : Nat} (v : Vec α n) (i : Fin n) : α :=
  getElem v i.val i.isLt

/--
Allow the use of `v[i]` notation.
-/
public instance {α : Type u} {n : Nat} : GetElem (Vec α n) Nat α inBounds where
  getElem := getElem

/--
Allow the use of `v[i]?` and `v[i]!` notations.
-/
public instance {α : Type u} {n : Nat} : GetElem? (Vec α n) Nat α inBounds :=
  inferInstance

/-!
### Finding elements
-/

/--
Return the index of the frontmost element that makes the predicate return `true`.
If not found, return `none`.
Takes time linear to returned index.
-/
public def find.{u} {α : Type u} {n : Nat} (p : α → Bool) : Vec α n → Option (Fin n)
  | nil => none
  | cons x xs =>
    bif p x then
      some ⟨0, by simp⟩
    else
      (λ ⟨i, _⟩ => ⟨i.succ, by simpa⟩) <$> xs.find p

/-!
### Splitting vector by length
-/

/--
Head of a nonempty vector.
`O(1)`.
-/
@[expose]
public abbrev head.{u} {α : Type u} {n : Nat} : Vec α n.succ → α
  | cons a _ => a

/--
Tail of a nonempty vector.
`O(1)`.
-/
@[expose]
public abbrev tail.{u} {α : Type u} {n : Nat} : Vec α n.succ → Vec α n
  | cons _ t => t

/--
Splits a vector into two, such that the front part has the supplied length.
`O(l)`.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `splitAt`, which has a simpler return type.
-/
public def splitAt'.{u} {α : Type u} {n : Nat} (l : Nat) (v :Vec α n) (hl : l ≤ n) : (m : Nat) × Vec α l × Vec α m ×' l + m = n :=
  match n, l, v with
  | n, 0, v => ⟨n, nil, v, by simp_all⟩
  | n' + 1, l' + 1, cons x xs =>
    let ⟨m, f, b, hs⟩ := xs.splitAt' l' (by simpa using hl)
    have : l' + 1 + m = n' + 1 := by calc l' + 1 + m
      _ = (l' + m) + 1 := by simp +arith only
      _ = n' + 1 := by rw [hs]
    ⟨m, cons x f, b, ‹_›⟩

/--
Splits a vector into two, such that the front part has the supplied length.
`O(l)`.

The lengths of the two returned vectors sum to `n`.
If you need the proof for theorem proving, use `splitAt'`.
-/
@[expose]
public abbrev splitAt.{u} {α : Type u} {n : Nat} (l : Nat) (v :Vec α n) (hl : l ≤ n) : (m : Nat) × Vec α l × Vec α m :=
  let ⟨m, f, b, _⟩ := v.splitAt' l hl
  ⟨m, f, b⟩

/--
Takes a prefix of length `l`.
`O(l)`.
-/
@[expose]
public abbrev take.{u} {α : Type u} {n : Nat} (l : Nat) (v : Vec α n) (hl : l ≤ n) : Vec α l :=
  let ⟨_, f, _, _⟩ := v.splitAt' l hl
  f

/--
Drops a prefix of length `l`, returning whatever is left.
`O(l)`.

This function returns more items than `drop`, because addition is easier to reason about than subtraction.
If you are programming, you might want to use the simpler `drop`.
-/
@[expose]
public abbrev drop'.{u} {α : Type u} {n : Nat} (l : Nat) (v : Vec α n) (hl : l ≤ n) : (m : Nat) × Vec α m ×' l + m = n :=
  let ⟨m, _, b, hs⟩ := v.splitAt' l hl
  ⟨m, b, hs⟩

/--
Drops a prefix of length `l`, returning whatever is left.
`O(l)`.

If you are programming (and not proving theorems), this function might be easier to handle than `drop'`.
However, casts might be needed to make the type fit.
-/
@[expose]
public abbrev drop.{u} {α : Type u} {n : Nat} (l : Nat) (v : Vec α n) (hl : l ≤ n) : Vec α (n - l) :=
  let ⟨m, _, b, hs⟩ := v.splitAt' l hl
  have : n - l = m := (Nat.sub_eq_iff_eq_add' hl).mpr hs.symm
  by simpa [*] using b

/-!
### Longest prefix satisfying predicate
-/

/--
Splits the vector into a longest prefix where every element satisfies the given predicate,
and a tail whose first element does not satisfy the predicate.
`O(l)`.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `splitBy`, which has a simpler return type.
-/
public def splitBy'.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (l m : Nat) × Vec α l × Vec α m ×' l + m = n :=
  match n, v with
  | 0, nil => ⟨0, 0, nil, nil, by simp⟩
  | n' + 1, cons x xs =>
    bif p x then
      let ⟨l, m, f, b, hs⟩ := xs.splitBy' p
      have : l + 1 + m = n' + 1 := by calc l + 1 + m
        _ = (l + m) + 1 := by simp +arith only
        _ = n' + 1 := by rw [hs]
      ⟨l + 1, m, cons x f, b, ‹_›⟩
    else
      ⟨0, n' + 1, nil, cons x xs, by simp⟩

/--
Splits the vector into a longest prefix where every element satisfies the given predicate,
and a tail whose first element does not satisfy the predicate.
`O(l)`.

The lengths of the two returned vectors sum to `n`.
If you need the proof for theorem proving, use `splitBy'`.
-/
@[expose]
public abbrev splitBy.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (l m : Nat) × Vec α l × Vec α m :=
  let ⟨l, m, f, b, _⟩ := v.splitBy' p
  ⟨l, m, f, b⟩

/--
Takes the longest prefix such that every element satisfies the given predicate.
`O(l)`.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `takeWhile`, which has a simpler return type.
-/
@[expose]
public abbrev takeWhile'.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (l : Nat) × Vec α l ×' l ≤ n :=
  let ⟨l, _, f, _, hs⟩ := v.splitBy' p
  ⟨l, f, Nat.le.intro hs⟩

/--
Takes the longest prefix such that every element satisfies the given predicate.
`O(l)`.

The length of the returned vector is `≤ n`.
If you need the proof for theorem proving, use `takeWhile'`.
-/
@[expose]
public abbrev takeWhile.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (l : Nat) × Vec α l :=
  let ⟨l, _, f, _, _⟩ := v.splitBy' p
  ⟨l, f⟩

/--
Repeatedly drops the head until the head does not satisfy the given predicate.
Takes time linear to the number of elements dropped.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `dropWhile`, which has a simpler return type.
-/
@[expose]
public abbrev dropWhile'.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (m : Nat) × Vec α m ×' m ≤ n :=
  let ⟨l, m, _, b, hs⟩ := v.splitBy' p
  have : m + l = n := by simpa +arith only
  have : m ≤ n := Nat.le.intro (k := l) ‹_›
  ⟨m, b, ‹_›⟩

/--
Repeatedly drops the head until the head does not satisfy the given predicate.
Takes time linear to the number of elements dropped.

The length of the returned vector is `≤ n`.
If you need the proof for theorem proving, use `dropWhile'`.
-/
@[expose]
public abbrev dropWhile.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (m : Nat) × Vec α m :=
  let ⟨_, m, _, b, _⟩ := v.splitBy' p
  ⟨m, b⟩

/-!
### Filter elements according to predicate
-/

/--
Partition the vector according to the given predicate.
The first returned vector contains elements that makes the predicate return true;
the second returned vector contains elements that makes the predicate return false.
`O(n)`.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `partition`, which has a simpler return type.
-/
public def partition'.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (a b : Nat) × Vec α a × Vec α b ×' a + b = n :=
  match n, v with
  | 0, nil => ⟨0, 0, nil, nil, by simp⟩
  | m + 1, cons x xs =>
    let ⟨a, b, pos, neg, hs⟩ := xs.partition' p
    bif p x then
      have : a + 1 + b = m + 1 := by calc a + 1 + b
        _ = (a + b) + 1 := by simp +arith only
        _ = m + 1 := by rw [hs]
      ⟨a + 1, b, cons x pos, neg, ‹_›⟩
    else
      have : a + b + 1 = m + 1 := by calc a + b + 1
        _ = (a + b) + 1 := by simp +arith only
        _ = m + 1 := by rw [hs]
      ⟨a, b + 1, pos, cons x neg, ‹_›⟩

/--
Partition the vector according to the given predicate.
The first returned vector contains elements that makes the predicate return true;
the second returned vector contains elements that makes the predicate return false.
`O(n)`.

The lengths of the two returned vectors sum to `n`.
If you need the proof for theorem proving, use `partition'`.
-/
@[expose]
public abbrev partition.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (a b : Nat) × Vec α a × Vec α b :=
  let ⟨a, b, pos, neg, _⟩ := v.partition' p
  ⟨a, b, pos, neg⟩

/--
Filter the vector, leaving only elements that satisfy the given predicate.
`O(n)`.

The proof could be useful for theorem proving.
If you are just programming, you might want to use `filter`, which has a simpler return type.
-/
@[expose]
public abbrev filter'.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (m : Nat) × Vec α m ×' m ≤ n :=
  let ⟨a, _, pos, _, hs⟩ := v.partition' p
  ⟨a, pos, Nat.le.intro hs⟩

/--
Filter the vector, leaving only elements that satisfy the given predicate.
`O(n)`.

The length of the returned vector is `≤ n`.
If you need the proof for theorem proving, use `filter`.
-/
@[expose]
public abbrev filter.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (m : Nat) × Vec α m :=
  let ⟨a, _, pos, _, _⟩ := v.partition' p
  ⟨a, pos⟩

/--
Count the number of elements in the vector satisfying the given predicate.
`O(n)`.

The returned proof could be usefule for theorem proving.
If you are just programming, you might want to use `count`, which has a simpler return type.
-/
@[expose]
public abbrev count'.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : (m : Nat) ×' m ≤ n :=
  let ⟨a, _, _, _, hs⟩ := v.partition' p
  ⟨a, Nat.le.intro hs⟩

/--
Count the number of elements in the vector satisfying the given predicate.
`O(n)`.

The returned count is `≤ n`.
If you need the proof for theorem proving, use `count'`.
-/
@[expose]
public abbrev count.{u} {α : Type u} {n : Nat} (p : α → Bool) (v : Vec α n) : Nat :=
  let ⟨a, _, _, _, _⟩ := v.partition' p
  a

/-!
### Folds
-/

/--
Left fold.
`O(n)`.
-/
public def foldl.{u, v} {α : Type u} {β : Type v} {n : Nat} (f : β → α → β) (b : β) : Vec α n → β
  | nil => b
  | cons x xs => xs.foldl f (f b x)

/--
Right fold.
`O(n)`.
-/
public def foldr.{u, v} {α : Type u} {β : Type v} {n : Nat} (f : α → β → β) (b : β) : Vec α n → β
  | nil => b
  | cons x xs => f x $ xs.foldr f b

/-!
### Appending vectors
-/

/--
Appends two vectors.
The resultant length is the sum of the lengths of the original vectors.
`O(m)`.
-/
public def append.{u} {α : Type u} {m n : Nat} : Vec α m → Vec α n → Vec α (m + n)
  | nil, bs => by simpa using bs
  | cons a as, bs => by simpa +arith using cons a (append as bs)

/--
Allow `++` notations.
-/
public instance {α : Type u} {m n : Nat} : HAppend (Vec α m) (Vec α n) (Vec α (m + n)) where
  hAppend := append

/-!
### Reversing vectors
-/

/--
Tail-recursively reverse `rem` and prepend the result onto `acc`.
Not to be called directly; use `reverse` to reverse a vector.
`O(n)`.
-/
public def reverseImplAux.{u} {α : Type u} {n a b : Nat} (acc : Vec α a) (rem : Vec α b) (hs : a + b = n) : Vec α n :=
  match _ : b, rem with
  | 0, nil =>
    have : a = n := by simpa
    by simpa [*] using acc
  | j + 1, cons x xs =>
    have : (a + 1) + j = n := by calc (a + 1) + j
      _ = a + (j + 1) := by simp +arith only
      _ = n := hs
    reverseImplAux (cons x acc) xs ‹_›

/--
Reverse a vector, using an efficient tail-recursive implementation.
Not to be called directly; use `reverse` to reverse a vector.
`O(n)`.
-/
@[expose]
public abbrev reverseImpl.{u} {α : Type u} {n : Nat} (v : Vec α n) : Vec α n :=
  reverseImplAux nil v (by simp)

/--
Reverse a vector using an inefficient but simple-to-reason algorithm.
Overriden in compiled code by `reverseImpl`.
The algorithm here is `O(n^2)`; the compiled algorithm is `O(n)`.
-/
@[implemented_by reverseImpl]
public def reverse.{u} {α : Type u} {n : Nat} : Vec α n → Vec α n
  | nil => nil
  | cons x xs => xs.reverse ++ singleton x

end Lean4Gists.Util.Vec

