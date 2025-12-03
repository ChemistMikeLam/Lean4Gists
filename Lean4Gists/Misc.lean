def ackermann : Nat → Nat → Nat
  | 0, n => n + 1
  | (m + 1), 0 => ackermann m 1
  | (m + 1), (n + 1) => ackermann m $ ackermann (m + 1) n
-- termination_by m n => (m, n)

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
