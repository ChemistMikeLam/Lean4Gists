module

namespace Lean4Gists.Data.List

public def append.{u} {α : Type u} : List α → List α → List α
  | [] => id
  | x :: xs => (x :: .) ∘ (append xs .)

public theorem nil_append_eq_id.{u} {α : Type u} (xs : List α) : append [] xs = xs := by
  simp [append]

public theorem nonempty_append_not_empty.{u} {α : Type u} (xs ys : List α) : xs ≠ [] → append xs ys ≠ [] := by
  cases xs with
  | nil => intro _ ; contradiction
  | cons x xs' => simp [append]

public theorem append_preserve_head.{u} {α : Type u} (xs ys : List α) (hxs : xs ≠ []) : xs.head hxs = (append xs ys).head (nonempty_append_not_empty xs ys hxs) := by
  unfold List.head
  cases xs with
  | nil => contradiction
  | cons x xs' => simp [append]

public theorem singleton_append_eq.{u} {α : Type u} (x y : α) (xs ys : List α) : [x] ++ xs = [y] ++ ys ↔ x = y ∧ xs = ys := by
  simp

public theorem append_singleton_eq.{u} {α : Type u} (x y : α) (xs ys : List α) : xs ++ [x] = ys ++ [y] ↔ xs = ys ∧ x = y := by
  apply Iff.intro
  case mp =>
    simp [List.append_eq_append_iff, List.singleton_eq_append_iff]
    intro
    | .inl ⟨as, ⟨hl, hm, hr⟩⟩
    | .inr ⟨as, ⟨hl, hm, hr⟩⟩ =>
      simp [hm] at hl
      symm_saturate
      trivial
  case mpr =>
    intro ⟨hl, hr⟩
    rw [hl, hr]

public def map.{u, v} {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | a :: as => f a :: map f as

public theorem map_nil_to_nil.{u, v} {α : Type u} {β : Type v} (f : α → β) : map f [] = [] := by
  simp [map]

public theorem map_preserve_length.{u, v} {α : Type u} {β : Type v} (f : α → β) (xs : List α) : xs.length = (map f xs).length := by
  induction xs with
  | nil => simp [map]
  | cons x xs' ih => simp [List.length, map, ih]

public theorem map_distribute_over_append.{u, v} {α : Type u} {β : Type v} (f : α → β) (xs ys : List α) : map f (append xs ys) = append (map f xs) (map f ys) := by
  induction xs with
  | nil => simp! [append, map]
  | cons x xs' ih => simp [append, map, ih]

public theorem reverse_eq.{u} {α : Type u} (xs ys : List α) : (xs = ys) ↔ (xs.reverse = ys.reverse) := by
  apply Iff.intro
  case mp =>
    intro h
    rw [h]
  case mpr =>
    match xs, ys with
    | [], []
    | [], _ :: _
    | _ :: _, [] => simp
    | x :: xs', y :: ys' =>
      simp [append_singleton_eq]
      intros
      trivial

end Lean4Gists.Data.List

