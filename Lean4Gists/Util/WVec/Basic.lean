/-
Copyright (c) 2026 ChemistMikeLam. All rights reserved.
Released under GNU General Public License version 3.0 or later.
See file LICENSE for a copy of the license.

Authors:
- ChemistMikeLam <43129403+ChemistMikeLam at users dot noreply dot github dot com>
-/

module

public import Lean4Gists.Util.Vec.Basic

/-!
# Length-indexed vectors, but wrapped

This file only contains defintions of datatype and functions.
Lemmas are put into `Lean4Gists.Util.WVec.Lemma`.

This module contains the type `Lean4Gists.Util.WVec`,
which is a wrapped version of `Lean4Gists.Util.Vec`.
The length information is no longer visible in the type,
but instead is stored in a field in the structure.
The lack of explicit length in type makes it easier to work with.
The price to pay is that possibly invalid operations,
which could be validated by the type system in `Lean4Gists.Util.Vec`,
now requires explicit proofs of validity.

Many of the functions available in this file are one-to-one correspondent to those in `Lean4Gists.Util.Vec.Basic`.
-/

namespace Lean4Gists.Util

/--
Length-indexed vectors, wrapped to hide the length in the type.
-/
public structure WVec.{u} (α : Type u) : Type u where
  /--
  Constructor.
  -/
  public mk ::

  /--
  Length of the wrapped vector.
  -/
  public length : Nat

  /--
  Wrapped vector.
  -/
  public vec : Vec α length

namespace WVec

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
for WVec

/-!
### Conversions
-/

/--
Convert a `Vec` into a `WVec`.
`O(1)`.
-/
@[expose]
public abbrev _root_.Lean4Gists.Util.Vec.toWVec.{u} {α : Type u} {n : Nat} (v : Vec α n) : WVec α :=
  ⟨n, v⟩

/--
Convert a `WVec` into a `Vec`.
`O(1)`.
-/
@[expose]
public abbrev toVec.{u} {α : Type u} (w : WVec α) : Vec α w.length :=
  w.vec

/--
Convert a `(n : Nat) × Vec α n` into a `WVec α`.
`O(1)`.
-/
@[expose]
public abbrev fromSigma.{u} {α : Type u} : (n : Nat) × Vec α n → WVec α
  | ⟨n, v⟩ => ⟨n, v⟩

/--
Convert a `WVec α` into a `(n : Nat) × Vec α n`.
`O(1)`.
-/
@[expose]
public abbrev toSigma.{u} {α : Type u} : WVec α → (n : Nat) × Vec α n
  | ⟨n, v⟩ => ⟨n, v⟩

/--
Convert a list into a `WVec`.
`O(l.length)`.
-/
@[expose]
public abbrev _root_.List.toWVec.{u} {α : Type u} (l : List α) : WVec α :=
  fromSigma l.toVec

/--
Convert a `WVec` into a list.
`O(w.length)`.
-/
@[expose]
public abbrev toList.{u} {α : Type u} (w : WVec α) : List α :=
  w.toVec.toList

/-!
### Constructing a wrapped vector from a seed
-/

/--
Wraps a value into a singleton wrapped vector.
`O(1)`.
-/
@[expose]
public abbrev singleton.{u} {α : Type u} (a : α) : WVec α :=
  Vec.singleton a |>.toWVec

/--
Generate a wrapped vector of length `n` from an element-generating function and a seed.
`O(n)`.
-/
@[expose]
public abbrev unfold_n.{u, v} {α : Type u} {β : Type v} (f : α → α × β) (seed : α) (n : Nat) : WVec β :=
  Vec.unfold_n f seed n |>.toWVec

/--
Generate a wrapped vector of length `n` where all elements are `a`.
`O(n)`.
-/
@[expose]
public abbrev ofRepeat.{u} {α : Type u} (a : α) (n : Nat) : WVec α :=
  Vec.ofRepeat a n |>.toWVec

/-!
### `Inhabited` and `Nonempty` instances
-/

/--
There is always an empty wrapped vector.
-/
public instance {α : Type u} : Inhabited (WVec α) where
  default := fromSigma default

/--
There is always an empty vector.
-/
public instance {α : Type u} : Nonempty (WVec α) :=
  inferInstance

/-!
### Possibly non-terminating vector generation
-/

/--
Generate a wrapped vector from an element-generating function and a seed.
Terminates when `f` returns `none`;
if `f` always return `some` this function will not terminate.
-/
@[expose]
public partial abbrev unfold.{u, v} {α : Type u} {β : Type v} (f : α → Option (α × β)) (seed : α) : WVec β :=
  fromSigma $ Vec.unfold f seed

/-!
### `Ord`, `LT`, `LE`, `Max` and `Min` instances
-/

/--
Imposes a dictionary order on the two wrapped vectors.
Takes time linear to length of shared prefix.
-/
@[expose]
public abbrev compare.{u} {α : Type u} [Ord α] : WVec α → WVec α → Ordering
  | ⟨_, a⟩, ⟨_, b⟩ => Vec.compare a b

/-!
Note that unlike the case for `Lean4Gists.Util.Vec`,
because the type does not include the length,
wrapped vectors of different lengths have the same type,
and thus could use the following notations.
-/

/--
Wrapped vectors have an ordering if the elemtents have an ordering.
-/
public instance {α : Type u} [Ord α] : Ord (WVec α) where
  compare := compare

/--
Allow use of `<` notation.
-/
public instance {α : Type u} [Ord α] : LT (WVec α) :=
  ltOfOrd

/--
`<` of wrapped vectors are decidable.
-/
public instance {α : Type u} [Ord α] : DecidableLT (WVec α) :=
  inferInstance

/--
Allow use of `≤` notation.
-/
public instance {α : Type u} [Ord α] : LE (WVec α) :=
  leOfOrd

/--
`≤` of wrapped vectors are decidable.
-/
public instance {α : Type u} [Ord α] : DecidableLE (WVec α) :=
  inferInstance

/--
Allow use of `Max.max`.
-/
public instance {α : Type u} [Ord α] : Max (WVec α) :=
  maxOfLe

/--
Allow use of `Min.min`.
-/
public instance {α : Type u} [Ord α] : Min (WVec α) :=
  minOfLe

/-!
### `Functor` interface
-/

/--
Standard `Functor` `map`, but allow map across universes.
`O(n)`.
-/
@[expose]
public abbrev map.{u, v} {α : Type u} {β : Type v} (f : α → β) : WVec α → WVec β
  | ⟨n, v⟩ => ⟨n, v.map f⟩

/--
Wrapped vectors are functors.
-/
public instance : Functor WVec where
  map := map

/-!
### Wrapped vector emptiness and in-bounds checks

Note that there is no corresponding function for `Lean4Gists.Util.Vec.length`;
the structure `WVec` already contains the field `length`.
-/

/--
An abbreviation for emptiness prop.
`O(1)`.
-/
@[expose]
public abbrev emptyProp.{u} {α : Type u} : WVec α → Prop
  | ⟨n, _⟩ => n = 0

/--
The emptiness prop is decidable.
-/
public instance {α : Type u} : @DecidablePred (WVec α) emptyProp :=
  inferInstance

/--
Emptiness check returning `Bool`.
`O(1)`.
-/
@[expose]
public abbrev isEmpty.{u} {α : Type u} (w : WVec α) : Bool :=
  decide w.emptyProp

/--
An abbreviation for in-bounds prop.
`O(1)`.
-/
@[expose]
public abbrev inBounds.{u} {α : Type u} : WVec α → Nat → Prop
  | ⟨n, _⟩ => (· < n)

/--
The in-bounds prop is decidable.
-/
public instance {α : Type u} : @DecidableRel (WVec α) Nat inBounds :=
  inferInstance

/--
In-bounds check returning `Bool`.
`O(1)`.
-/
@[expose]
public abbrev isInBounds.{u} {α : Type u} (w : WVec α) (i : Nat) : Bool :=
  decide (w.inBounds i)

/-!
### `GetElem` interface

These functions cannot ensure that the wrapped vector length not be 0 in the type.
However, because you have to construct a proof that the index is less than the length,
and there being no way to construct the proof if the wrapped vector has zero length,
they effectively only allow indexing into nonempty wrapped vectors.
(With the exception of `w[i]!`, which does not require any proof, and would panic when you use it on an empty vector.)
-/

/--
Gets the `i`th element of the vector.
Requires proof that the index is in bounds.
`O(i)`.
-/
@[expose]
public abbrev getElem.{u} {α : Type u} (w : WVec α) (i : Nat) (h : inBounds w i) : α :=
  w.vec.getElem i h

/--
Similar to `getElem`, but use `Fin`, which carries the needed proof.
`O(i)`.
-/
public abbrev getElemFin.{u} {α : Type u} (w : WVec α) (i : Fin w.length) : α :=
  getElem w i.val i.isLt

/--
Allow the use of `w[i]` notation.
-/
public instance {α : Type u} : GetElem (WVec α) Nat α inBounds where
  getElem := getElem

/--
Allow the use of `w[i]?` and `w[i]!` notations.
-/
public instance {α : Type u} : GetElem? (WVec α) Nat α inBounds :=
  inferInstance

/-!
### Finding elements
-/

/--
Return the index of the frontmost element that makes the predicate return `true`.
If not found, return `none`.
Takes time linear to returned index.
-/
@[expose]
public abbrev find.{u} {α : Type u} (p : α → Bool) (w : WVec α) : Option (Fin w.length) :=
  w.vec.find p

/-!
### Splitting wrapped vector by length
-/

/--
Head of a nonempty wrapped vector.
Unlike `Lean4Gists.Util.Vec.head`, takes a proof of nonemptiness.
`O(1)`.
-/
@[expose]
public abbrev head.{u} {α : Type u} (w : WVec α) (h : ¬ w.emptyProp) : α :=
  match h' : w.length with
  | 0 => absurd h' h
  | n + 1 =>
    let v : Vec α n.succ := (congr rfl h').mp w.vec
    v.head

/--
Tail of a nonempty wrapped vector.
Unlike `Lean4Gists.Util.Vec.tail`, takes a proof of nonemptiness.
`O(1)`.
-/
@[expose]
public abbrev tail.{u} {α : Type u} (w : WVec α) (h : ¬ w.emptyProp) : WVec α :=
  match h' : w.length with
  | 0 => absurd h' h
  | n + 1 =>
    let v : Vec α n.succ := (congr rfl h').mp w.vec
    v.tail.toWVec

/--
Splits a wrapped vector into two, such that the front part has the supplied length.
`O(l)`.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `splitAt`, which has a simpler return type.
-/
@[expose]
public abbrev splitAt'.{u}
    {α : Type u}
    (l : Nat)
    (w : WVec α)
    (hl : l ≤ w.length)
    : (f : WVec α) × (b : WVec α) ×' f.length + b.length = w.length :=
  let ⟨_, f, b, _⟩ := w.vec.splitAt' l hl
  ⟨f.toWVec, b.toWVec, ‹_›⟩

/--
Splits a wrapped vector into two, such that the front part has the supplied length.
`O(l)`.

The lengths of the two returned wrapped vectors sum to `w.length`.
If you need the proof for theorem proving, use `splitAt'`.
-/
@[expose]
public abbrev splitAt.{u} {α : Type u} (l : Nat) (w :WVec α) (hl : l ≤ w.length) : WVec α × WVec α :=
  let ⟨_, f, b, _⟩ := w.vec.splitAt' l hl
  (f.toWVec, b.toWVec)

/--
Takes a prefix of length `l`.
`O(l)`.
-/
@[expose]
public abbrev take.{u} {α : Type u} (l : Nat) (w : WVec α) (hl : l ≤ w.length) : WVec α :=
  let ⟨_, f, _, _⟩ := w.vec.splitAt' l hl
  f.toWVec

/--
Drops a prefix of length `l`, returning whatever is left.
`O(l)`.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `drop`, which has a simpler return type.
-/
@[expose]
public abbrev drop'.{u} {α : Type u} (l : Nat) (w : WVec α) (hl : l ≤ w.length) : (w' : WVec α) ×' l + w'.length = w.length :=
  let ⟨_, _, b, _⟩ := w.vec.splitAt' l hl
  ⟨b.toWVec, ‹_›⟩

/--
Drops a prefix of length `l`, returning whatever is left.
`O(l)`.

The length of the returned wrapped vector is `w.length - l`.
If you need the proof for theorem proving, use `drop'`.
-/
@[expose]
public abbrev drop.{u} {α : Type u} (l : Nat) (w : WVec α) (hl : l ≤ w.length) : WVec α :=
  let ⟨_, _, b, _⟩ := w.vec.splitAt' l hl
  b.toWVec

/-!
### Longest prefix satisfying predicate
-/

/--
Splits the wrapped vector into a longest prefix where every element satisfies the given predicate,
and a tail whose first element does not satisfy the predicate.
Takes time linear to the length of the first returned wrapped vector.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `splitBy`, which has a simpler return type.
-/
@[expose]
public abbrev splitBy'.{u}
    {α : Type u}
    (p : α → Bool)
    (w : WVec α)
    : (f : WVec α) × (b : WVec α) ×' f.length + b.length = w.length :=
  let ⟨_, _, f, b, _⟩ := w.vec.splitBy' p
  ⟨f.toWVec, b.toWVec, ‹_›⟩

/--
Splits the wrapped vector into a longest prefix where every element satisfies the given predicate,
and a tail whose first element does not satisfy the predicate.
Takes time linear to the length of the first returned wrapped vector.

The lengths of the two returned vectors sum to `w.length`.
If you need the proof for theorem proving, use `splitBy'`.
-/
@[expose]
public abbrev splitBy.{u} {α : Type u} (p : α → Bool) (w : WVec α) : WVec α × WVec α :=
  let ⟨_, _, f, b, _⟩ := w.vec.splitBy' p
  (f.toWVec, b.toWVec)

/--
Takes the longest prefix such that every element satisfies the given predicate.
Takes time linear to the returned prefix.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `takeWhile`, which has a simpler return type.
-/
@[expose]
public abbrev takeWhile'.{u}
    {α : Type u}
    (p : α → Bool)
    (w : WVec α)
    : (w' : WVec α) ×' w'.length ≤ w.length :=
  let ⟨_, _, f, _, hs⟩ := w.vec.splitBy' p
  ⟨f.toWVec, Nat.le.intro hs⟩

/--
Takes the longest prefix such that every element satisfies the given predicate.
Takes time linear to the returned prefix.

The length of the returned vector is `≤ w.length`.
If you need the proof for theorem proving, use `takeWhile'`.
-/
@[expose]
public abbrev takeWhile.{u} {α : Type u} (p : α → Bool) (w : WVec α) : WVec α :=
  let ⟨_, _, f, _, _⟩ := w.vec.splitBy' p
  f.toWVec

/--
Repeatedly drops the head until the head does not satisfy the given predicate.
Takes time linear to the number of elements dropped.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `dropWhile`, which has a simpler return type.
-/
@[expose]
public abbrev dropWhile'.{u}
    {α : Type u}
    (p : α → Bool)
    (w : WVec α)
    : (w' : WVec α) ×' w'.length ≤ w.length :=
  let ⟨l, m, _, b, hs⟩ := w.vec.splitBy' p
  have : m + l = w.length := by simpa +arith only
  have : m ≤ w.length := Nat.le.intro (k := l) ‹_›
  ⟨b.toWVec, ‹_›⟩

/--
Repeatedly drops the head until the head does not satisfy the given predicate.
Takes time linear to the number of elements dropped.

The length of the returned vector is `≤ w.length`.
If you need the proof for theorem proving, use `dropWhile'`.
-/
@[expose]
public abbrev dropWhile.{u} {α : Type u} (p : α → Bool) (w : WVec α) : WVec α :=
  let ⟨_, _, _, b, _⟩ := w.vec.splitBy' p
  b.toWVec

/-!
### Filter elements according to predicate
-/

/--
Partition the wrapped vector according to the given predicate.
The first returned vector contains elements that makes the predicate return true;
the second returned vector contains elements that makes the predicate return false.
`O(w.length)`.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `partition`, which has a simpler return type.
-/
@[expose]
public abbrev partition'.{u}
    {α : Type u}
    (p : α → Bool)
    (w : WVec α)
    : (pos : WVec α) × (neg : WVec α) ×' pos.length + neg.length = w.length :=
  let ⟨_, _, pos, neg, _⟩ := w.vec.partition' p
  ⟨pos.toWVec, neg.toWVec, ‹_›⟩

/--
Partition the wrapped vector according to the given predicate.
The first returned vector contains elements that makes the predicate return true;
the second returned vector contains elements that makes the predicate return false.
`O(w.length)`.

The lengths of the two returned wrapped vectors sum to `w.lerngth`.
If you need the proof for theorem proving, use `partition'`.
-/
@[expose]
public abbrev partition.{u} {α : Type u} (p : α → Bool) (w : WVec α) : WVec α × WVec α :=
  let ⟨_, _, pos, neg, _⟩ := w.vec.partition' p
  ⟨pos.toWVec, neg.toWVec⟩

/--
Filter the wrapped vector, leaving only elements that satisfy the given predicate.
`O(w.length)`.

The proof could be useful for theorem proving.
If you are just programming, you might want to use `filter`, which has a simpler return type.
-/
@[expose]
public abbrev filter'.{u} {α : Type u} (p : α → Bool) (w : WVec α) : (w' : WVec α) ×' w'.length ≤ w.length :=
  let ⟨_, _, pos, _, hs⟩ := w.vec.partition' p
  ⟨pos.toWVec, Nat.le.intro hs⟩

/--
Filter the wrapped vector, leaving only elements that satisfy the given predicate.
`O(w.length)`.

The length of the returned wrapped vector is `≤ w.length`.
If you need the proof for theorem proving, use `filter`.
-/
@[expose]
public abbrev filter.{u} {α : Type u} (p : α → Bool) (w : WVec α) : WVec α :=
  let ⟨_, _, pos, _, _⟩ := w.vec.partition' p
  pos.toWVec

/--
Count the number of elements in the wrapped vector satisfying the given predicate.
`O(w.length)`.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `count`, which has a simpler return type.
-/
@[expose]
public abbrev count'.{u} {α : Type u} (p : α → Bool) (w : WVec α) : (m : Nat) ×' m ≤ w.length :=
  let ⟨a, _, _, _, hs⟩ := w.vec.partition' p
  ⟨a, Nat.le.intro hs⟩

/--
Count the number of elements in the wrapped vector satisfying the given predicate.
`O(w.length)`.

The returned count is `≤ w.length`.
If you need the proof for theorem proving, use `count'`.
-/
@[expose]
public abbrev count.{u} {α : Type u} (p : α → Bool) (w : WVec α) : Nat :=
  let ⟨a, _, _, _, _⟩ := w.vec.partition' p
  a

/-!
### Folds
-/

/--
Left fold.
`O(w.length)`.
-/
@[expose]
public abbrev foldl.{u, v} {α : Type u} {β : Type v} (f : β → α → β) (b : β) (w : WVec α) : β :=
  w.vec.foldl f b

/--
Right fold.
`O(w.length)`.
-/
@[expose]
public abbrev foldr.{u, v} {α : Type u} {β : Type v} (f : α → β → β) (b : β) (w : WVec α) : β :=
  w.vec.foldr f b

/-!
### Appending wrapped vectors
-/

/--
Appends two wrapped vectors.
`O(f.length)`.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `append`, which has a simpler return type.
-/
@[expose]
public abbrev append'.{u} {α : Type u} (f b : WVec α) : (w : WVec α) ×' w.length = f.length + b.length :=
  ⟨f.vec.append b.vec |>.toWVec, rfl⟩

/--
Appends two wrapped vectors.
`O(f.length)`.

The resultant length is the sum of the lengths of the original wrapped vectors.
If you need the proof, use `append'`.
-/
@[expose]
public abbrev append.{u} {α : Type u} (f b : WVec α) : WVec α :=
  f.vec.append b.vec |>.toWVec

/-!
### Reversing wrapped vectors
-/

/--
Reverse a wrapped vector.
`O(w.length)`.

The returned proof could be useful for theorem proving.
If you are just programming, you might want to use `reverse`, which has a simpler return type.
-/
@[expose]
public abbrev reverse'.{u} {α : Type u} (w : WVec α) : (w' : WVec α) ×' w'.length = w.length :=
  ⟨w.vec.reverse.toWVec, rfl⟩

/--
Reverse a wrapped vector.
`O(w.length)`.

The returned wrapped vector has the same length as the input.
If you need the proof, use `reverse'`.
-/
@[expose]
public abbrev reverse.{u} {α : Type u} (w : WVec α) : WVec α :=
  w.vec.reverse.toWVec

end Lean4Gists.Util.WVec

