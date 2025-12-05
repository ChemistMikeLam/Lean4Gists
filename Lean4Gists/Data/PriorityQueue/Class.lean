module

namespace Lean4Gists
namespace Data

/--
-/
public class PriorityQueue.{u, v, w} (Q : (α : Type u) → (f : α → α → Ordering) → Type v → Type w) where

  /--
  -/
  public empty {α : Type u} {f : α → α → Ordering} {β : Type v} : Q α f β
  /--
  -/
  public isEmpty {α : Type u} {f : α → α → Ordering} {β : Type v} (q : Q α f β) : Bool
  /--
  -/
  public findMin {α : Type u} {f : α → α → Ordering} {β : Type v} (q : Q α f β) (h : ¬ isEmpty q) : α × β
    /--
  -/
  public findMin? {α : Type u} {f : α → α → Ordering} {β : Type v} (q : Q α f β) : Option (α × β)
    /--
  -/
  public findMin! {α : Type u} {f : α → α → Ordering} {β : Type v} (q : Q α f β) : α × β
    /--
  -/
  public deleteMin {α : Type u} {f : α → α → Ordering} {β : Type v} (q : Q α f β) : Q α f β
    /--
  -/
  public insert {α : Type u} {f : α → α → Ordering} {β : Type v} (k : α) (v : β) (q : Q α f β) : Q α f β
    /--
  -/
  public merge {α : Type u} {f : α → α → Ordering} {β : Type v} (ql qr : Q α f β) : Q α f β

end Data
end Lean4Gists

