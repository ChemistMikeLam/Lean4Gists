/-
Copyright (c) 2025 ChemistMikeLam. All rights reserved.
Released under GNU General Public License version 3.0 or later.
See file LICENSE for a copy of the license.

Authors:
- ChemistMikeLam <43129403+ChemistMikeLam at users dot noreply dot github dot com>
-/

module

public import Lean4Gists.Data.Queue.Class

/-!
# FIFO queue by two lists

This is the "standard" implementation of a persistent FIFO queue using two linked lists,
representing the front and the reversed back of the queue respectively.

This implementation provides for O(1) enqueueing and amortised O(1) dequeueing.
-/

namespace Lean4Gists.Data.Queue

/--
A FIFO queue consisting of two lists.

The constructor is made private; to modify the queues use the public API provided.
-/
public structure BiListQ.{u} (α : Type u) : Type u where
  /--
  Constructor. Made private.
  -/
  private mk ::
  /--
  Front part of the queue.
  -/
  public front : List α
  /--
  Back part of the queue, stored in reverse.
  -/
  public back : List α
  deriving Repr, Nonempty, Inhabited, BEq, Hashable, Ord

namespace BiListQ

/-!
### `Queue` interface
-/

/-!
#### Empty queue and emptiness check
-/

/--
Empty queue.
-/
public def empty.{u} {α : Type u} : BiListQ α := ⟨[], []⟩

/--
Test for emptiness.
-/
public def isEmpty.{u} {α : Type u} : BiListQ α → Bool
  | ⟨[], []⟩ => true
  | _ => false

/--
Helper theorem.

`empty` `isEmpty`.
-/
public theorem empty_isEmpty.{u} {α : Type u} : (@empty α).isEmpty := by
  simp [BiListQ.empty, BiListQ.isEmpty]

/--
Helper theorem for queue emptiness.

The queue is empty iff both the front and back are empty.
-/
@[simp]
public theorem empty_iff_both_empty.{u} {α : Type u} {q : BiListQ α} : q.isEmpty ↔ q.front = [] ∧ q.back = [] := by
  match q with
  | ⟨[], []⟩ | ⟨_ :: _, _⟩ | ⟨_, _ :: _⟩ => simp [BiListQ.isEmpty]

/--
Helper theorem.

If the queue is empty, then the front part is empty.
-/
@[simp]
public theorem empty_front_of_empty.{u} {α : Type u} {q : BiListQ α} : q.isEmpty → q.front = [] :=
  And.left ∘ q.empty_iff_both_empty.mp

/--
Helper theorem.

If the queue is empty, then the back part is empty.
-/
@[simp]
public theorem empty_back_of_empty.{u} {α : Type u} {q : BiListQ α} : q.isEmpty → q.back = [] :=
  And.right ∘ q.empty_iff_both_empty.mp

/--
Helper theorem.

If the front part is not empty, then the queue is not empty.
-/
@[simp]
public theorem nonempty_of_nonempty_front.{u} {α : Type u} {q : BiListQ α} : q.front ≠ [] → ¬ q.isEmpty := by
  intro hfne hqe
  exact hfne $ q.empty_front_of_empty hqe

/--
Helper theorem.

If the back of the queue is not empty, then the queue is not empty.
-/
@[simp]
public theorem nonempty_of_nonempty_back.{u} {α : Type u} {q : BiListQ α} : q.back ≠ [] → ¬ q.isEmpty := by
  intro hbne hqe
  exact hbne $ q.empty_back_of_empty hqe

/--
Helper function.
Eliminiator given a proof of nonemptiness.

`ffne` is a function to be used when the front part is not empty.
It takes the head of the queue, as well as the two parts of the queue in order, and returns a `β`.

`ffe` is a function to be used when the front part is empty.
It takes the head and tail of the queue, and returns a `β`.
-/
public def with_proof_nonempty.{u, v}
    {α : Type u}
    {β : Type v}
    (ffne : α → List α → List α → β)
    (ffe : α → List α → β)
    : (q : BiListQ α) → (¬ q.isEmpty) → β
  | ⟨a :: f, b⟩, _ => ffne a f b
  | ⟨[], b@hb : (_ :: _)⟩, _ =>
    let r : List α := b.reverse
    have : r ≠ [] := List.reverse_ne_nil_iff.mpr (by simp [hb])
    let h :: t := r
    ffe h t

/-!
#### Enqueueing
-/

/--
Enques to the end of the queue.
O(1) always.
-/
public def enqueue.{u} {α : Type u} (a : α) : BiListQ α → BiListQ α
  | ⟨f, b⟩ => ⟨f, a :: b⟩

/-!
#### Peek, tail and dequeueing
-/

/--
Peeks at the front of the queue.
Requires a proof of nonemptiness.

If you also need the remaining queue, use `dequeue` for better perforamnce.
-/
public def peek.{u} {α : Type u} (q : BiListQ α) : (¬ q.isEmpty) → α :=
  q.with_proof_nonempty
    (λ a _ _ => a)
    (λ a _ => a)

/--
Get the tail of the queue, that is, the remaining queue after the front element is removed.
Requires a proof of nonemptiness.
O(1) amortised.

If you also need the front element, use `dequeue` for better perforamnce.
-/
public def tail.{u} {α : Type u} (q : BiListQ α) : (¬ q.isEmpty) → BiListQ α :=
  q.with_proof_nonempty
    (λ _ f b => ⟨f, b⟩)
    (λ _ t => ⟨t, []⟩)

/--
Dequeue the front element, returning both the removed element and the remaning queue.
Requires a proof of nonemptiness.
O(1) amortised.
-/
public def dequeue.{u} {α : Type u} (q : BiListQ α) : (¬ q.isEmpty) → α × BiListQ α :=
  q.with_proof_nonempty
    (λ a f b => (a, ⟨f, b⟩))
    (λ h t => (h, ⟨t, []⟩))

/-!
#### `Queue` instance
-/

/--
`BiListQ` is a `Queue`.
-/
public instance : Queue BiListQ where
  empty := empty
  isEmpty := isEmpty
  enqueue := enqueue
  peek := peek
  tail := tail
  dequeue := dequeue

/-!
### `Functor` interface
-/

/--
Normal `Functor` `map`.
-/
public def map.{u, v} {α : Type u} {β : Type v} (f : α → β) : BiListQ α → BiListQ β
  | ⟨fr, b⟩ => ⟨fr.map f, b.map f⟩

/--
This queue is a functor.
This instance should have a better performance than the one in the `Queue` class interface.
-/
public instance : Functor BiListQ where
  map := map

end Lean4Gists.Data.Queue.BiListQ

