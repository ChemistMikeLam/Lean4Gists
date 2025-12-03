module

namespace Lean4Gists.Data.LeafTree

public inductive LeafTree.{u} (α : Type u) : Type u
  | Empty : LeafTree α
  | Leaf (a : α) : LeafTree α
  | Branch (left right : LeafTree α) : LeafTree α
  deriving Repr, Nonempty

public def LeafTree.map.{u} {α β : Type u} (f : α -> β) : LeafTree α -> LeafTree β
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

end Lean4Gists.Data.LeafTree

