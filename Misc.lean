def ackermann : Nat → Nat → Nat
  | 0, n => n + 1
  | (m + 1), 0 => ackermann m 1
  | (m + 1), (n + 1) => ackermann m $ ackermann (m + 1) n
-- termination_by m n => (m, n)

section List

universe u v
variable
  {α : Type u}
  {β : Type v}
  (f : α → β)
  (xs ys : List α)
  (x y : α)

def append : List α → List α → List α
  | [] => id
  | x :: xs => (x :: .) ∘ (append xs .)

theorem nil_append_eq_id : append [] xs = xs := by
  simp [append]

theorem nonempty_append_not_empty : xs ≠ [] → append xs ys ≠ [] := by
  cases xs with
  | nil => intro _ ; contradiction
  | cons x xs' => simp [append]

theorem append_preserve_head : ∀ (hxs : xs ≠ []), xs.head hxs = (append xs ys).head (nonempty_append_not_empty xs ys hxs) := by
  unfold List.head
  cases xs with
  | nil => intro _ ; contradiction
  | cons x xs' => simp [append]

theorem singleton_append_eq : [x] ++ xs = [y] ++ ys ↔ x = y ∧ xs = ys := by
  simp

theorem append_singleton_eq : xs ++ [x] = ys ++ [y] ↔ xs = ys ∧ x = y := by
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

def map : (α → β) → List α → List β :=
  λ f => λ
  | [] => []
  | a :: as => f a :: map f as

theorem map_nil_to_nil : map f [] = [] := by
  simp [map]

theorem map_preserve_length : xs.length = (map f xs).length := by
  induction xs with
  | nil => simp [map]
  | cons x xs' ih => simp [List.length, map, ih]

theorem map_distribute_over_append : map f (append xs ys) = append (map f xs) (map f ys) := by
  induction xs with
  | nil => simp! [append, map]
  | cons x xs' ih => simp [append, map, ih]

theorem reverse_eq : (xs = ys) ↔ (xs.reverse = ys.reverse) := by
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

end List

section LeafTree

universe u
variable
  {α β : Type u}

inductive LeafTree (α : Type u) : Type (u + 1)
  | Empty : LeafTree α
  | Leaf : α -> LeafTree α
  | Branch : LeafTree α -> LeafTree α -> LeafTree α
  deriving Repr

def LeafTree.map : (α -> β) -> LeafTree α -> LeafTree β :=
  λ f => λ
  | .Empty => LeafTree.Empty
  | .Leaf a => LeafTree.Leaf $ f a
  | .Branch l r => LeafTree.Branch (l.map f) (r.map f)

instance : Functor LeafTree where
  map := LeafTree.map

instance : LawfulFunctor LeafTree where
  map_const := by simp [Functor.map, Functor.mapConst]
  id_map := by
    simp [Functor.map]
    intro _ t
    induction t with
    | Empty => simp [LeafTree.map]
    | Leaf _ => simp [LeafTree.map]
    | Branch _ _ ihl ihr => simp [LeafTree.map, ihl, ihr]
  comp_map := by
    simp [Functor.map]
    intro _ _ _ _ _ t
    induction t with
    | Empty => simp [LeafTree.map]
    | Leaf _ => simp [LeafTree.map]
    | Branch _ _ ihl ihr => simp [LeafTree.map, ihl, ihr]

end LeafTree
