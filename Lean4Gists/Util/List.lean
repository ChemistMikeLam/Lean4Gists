/-
Copyright (c) 2025 ChemistMikeLam. All rights reserved.
Released under GNU General Public License version 3.0 or later.
See file LICENSE for a copy of the license.

Authors:
- ChemistMikeLam <43129403+ChemistMikeLam at users dot noreply dot github dot com>
-/

module

/-!
# `List` utilities
-/

namespace Lean4Gists.Util.List

/-!
### Custom `append` and helper theorems
-/

/--
Custom version of `List.append`.
-/
@[expose]
public def append.{u} {α : Type u} : List α → List α → List α
  | [] => id
  | x :: xs => (x :: ·) ∘ (append xs ·)

/--
The custom `append` is equivalent to the original `List.append`.
-/
@[simp]
public theorem append_eq_List_append.{u} {α : Type u} {xs ys : List α} : append xs ys = xs ++ ys := by
  induction xs with
  | nil => simp!
  | cons _ _ ih => simpa! using ih

/--
Prepending an empty list does nothing.
-/
@[simp]
public theorem nil_append_eq_id.{u} {α : Type u} {xs : List α} : append [] xs = xs := by
  simp!

/--
Prepending a nonempty list results in a nonempty list.
-/
@[simp]
public theorem nonempty_append_not_empty.{u} {α : Type u} {xs ys : List α} (_ : xs ≠ [] := by decide) : append xs ys ≠ [] := by
  cases xs with
  | nil => contradiction
  | cons _ _ => simp!

/--
Appending any list at the end does not change the head of a nonempty list.
-/
@[simp]
public theorem append_preserve_head.{u} {α : Type u} {xs ys : List α} {hxs : xs ≠ []} : (append xs ys).head (nonempty_append_not_empty hxs) = xs.head hxs := by
  unfold List.head
  cases xs with
  | nil => contradiction
  | cons _ _ => simp!

/--
Given two lists, both of which can be written in the form of a singleton prepended to another list.
If the two lists are equal, then both the element in the singleton and the appended list are respectively equal.
-/
@[simp]
public theorem singleton_append_eq.{u} {α : Type u} {x y : α} {xs ys : List α} : append [x] xs = append [y] ys ↔ x = y ∧ xs = ys := by
  simp

/--
Given two lists, both of which can be written in the form of a singleton appended to another list.
If the two lists are equal, then both the element in the singleton and the prepended list are respectively equal.
-/
@[simp]
public theorem append_singleton_eq.{u} {α : Type u} {x y : α} {xs ys : List α} : append xs [x] = append ys [y] ↔ xs = ys ∧ x = y := by
  refine ⟨?mp, ?mpr⟩
  case mp =>
    simp [List.append_eq_append_iff, List.singleton_eq_append_iff]
    intro
    | .inl ⟨_, ⟨hl, hm, _⟩⟩
    | .inr ⟨_, ⟨hl, hm, _⟩⟩ =>
      simp [hm] at hl
      symm_saturate
      trivial
  case mpr =>
    intro ⟨hl, hr⟩
    rw [hl, hr]

/-!
### Custom `map` and helper theorems
-/

/--
Custom version of `List.map`.
-/
@[expose]
public def map.{u, v} {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | a :: as => f a :: map f as

/--
The custom `map` is equivalent to the original `List.map`.
-/
@[simp]
public theorem map_eq_List_map.{u} {α β : Type u} {f : α → β} {xs : List α} : map f xs = xs.map f := by
  induction xs with
  | nil => simp!
  | cons _ _ ih => simpa! using ih

/--
Empty lists are mapped to empty lists.
-/
@[simp]
public theorem map_nil_to_nil.{u, v} {α : Type u} {β : Type v} {f : α → β} : map f [] = [] := by
  simp!

/--
`map` preserves the `List.length` of lists.
-/
@[simp]
public theorem map_preserve_length.{u, v} {α : Type u} {β : Type v} {f : α → β} {xs : List α} : (map f xs).length = xs.length := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simpa! using ih

/--
`map` distributes over `append`.
-/
@[simp]
public theorem map_distribute_over_append.{u, v} {α : Type u} {β : Type v} {f : α → β} {xs ys : List α} : map f (append xs ys) = append (map f xs) (map f ys) := by
  induction xs with
  | nil => simp!
  | cons _ _ ih => simpa! using ih

/-!
### `List.reverse` helper theorems
-/

/--
If two lists are equal, then their reverse are equal.
-/
@[simp]
public theorem reverse_eq.{u} {α : Type u} {xs ys : List α} : (xs.reverse = ys.reverse) ↔ (xs = ys) := by
  refine ⟨?mp, ?mpr⟩
  case mp =>
    match xs, ys with
    | [], []
    | [], _ :: _
    | _ :: _, [] => simp
    | x :: xs', y :: ys' =>
      simp
      exact flip And.intro
  case mpr =>
    intro h
    rw [h]

/-!
### Collate equal items
-/

/--
Insert an element at the end of list, if it was not in the list to begin with.
-/
@[expose]
public def insert_undup.{u} {α : Type u} [BEq α] (x : α) : List α → List α
  | [] => [x]
  | xs@(x' :: xs') =>
    if x == x' then
      xs
    else
      x' :: insert_undup x xs'

/--
Remove duplicate elements, keeping the first appearance.
-/
@[expose]
public def collate.{u} {α : Type u} [BEq α] : List α → List α :=
  let rec /--
  Insert all unique elements in the second argument into the first argument, skipping if it already is in there.
  -/
  go (acc : List α) : List α → List α
    | [] => acc
    | x :: xs => go (insert_undup x acc) xs
  go []

/-!
### Subsequences
-/

/--
Generate the power set of a list.
-/
@[expose]
public def subseqs.{u} {α : Type u} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    let rem : List (List α) := subseqs xs
    rem.map (x :: ·) ++ rem

end Lean4Gists.Util.List

