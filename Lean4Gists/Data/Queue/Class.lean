/-
Copyright (c) 2025 ChemistMikeLam. All rights reserved.
Released under GNU General Public License version 3.0 or later.
See file LICENSE for a copy of the license.

Authors:
- ChemistMikeLam <43129403+ChemistMikeLam at users dot noreply dot github dot com>
-/

module

/-!
# FIFO queues - Interface

This module contains the interface `Lean4Gists.Data.Queue` for FIFO queues.

For a list of implementations, as well as other perculiarites, consult the documentation of the parent module.
-/

namespace Lean4Gists.Data

/--
Interface for FIFO queues.

A datatype `Q` that implements this interface contains elements of any type α in any universe.

This datatype should have an empty collection state, and support the following operations:
- emptiness check
- enqueueing at the end of the queue
- dequeueing, returning either the front element, the remaining queue, or both

Minimum required set:
- `empty`
- `isEmpty`
- `enqueue`
- `peek`
- `tail`
-/
public class Queue.{u, v} (Q : Type u → Type v) : Type (max (u + 1) v) where

  /--
  The empty queue.
  -/
  public empty {α : Type u} : Q α

  /--
  Emptiness check.
  -/
  public isEmpty {α : Type u} (q : Q α) : Bool

  /--
  Enqueue at the end.
  -/
  public enqueue {α : Type u} (a : α) (q : Q α) : Q α

  /--
  Peek at the front element.
  Requires a proof of nonemptiness.
  -/
  public peek {α : Type u} (q : Q α) (h : ¬ isEmpty q) : α

  /--
  Similar to `peek`, but not require proof.
  Returns an `Option`.
  Instances may want to redefine using a more efficient implementation.
  -/
  public peek? {α : Type u} (q : Q α) : Option α :=
    if h : isEmpty q then none else some $ peek q h

  /--
  Similar to `peek`, but not require proof.
  Panics if queue is empty.
  Instances may want to redefine using a more efficient implementation.
  -/
  public peek! {α : Type u} [Inhabited α] (q : Q α) : α :=
    if h : isEmpty q then panic "Empty queue" else peek q h

  /--
  Get the queue with the front element removed.
  Requires a proof of nonemptiness.
  -/
  public tail {α : Type u} (q : Q α) (h : ¬ isEmpty q) : Q α

  /--
  Similar to `tail`, but not require proof.
  Returns an `Option`.
  Instances may want to redefine using a more efficient implementation.
  -/
  public tail? {α : Type u} (q : Q α) : Option (Q α) :=
    if h : isEmpty q then none else some $ tail q h

  /--
  Similar to `tail`, but not require proof.
  Panics if queue is empty.
  Instances may want to redefine using a more efficient implementation.
  -/
  public tail! {α : Type u} [Inhabited (Q α)] (q : Q α) : Q α :=
    if h : isEmpty q then panic "Empty queue" else tail q h

  /--
  Dequeues the front element, and return both the dequeued element and the remaining queue.
  Requires proof of nonemptiness.
  Instances may want to redefine using a more efficient implementation.
  -/
  public dequeue {α : Type u} (q : Q α) (h : ¬ isEmpty q) : α × Q α :=
    (peek q h, tail q h)

  /--
  Similar to `dequeue`, but not require proof.
  Returns an `Option`.
  Instances may want to redefine using a more efficient implementation.
  -/
  public dequeue? {α : Type u} (q : Q α) : Option (α × Q α) :=
    if h : isEmpty q then none else some $ dequeue q h

  /--
  Similar to `dequeue`, but not require proof.
  Panics if queue is empty.
  Instances may want to redefine using a more efficient implementation.
  -/
  public dequeue! {α : Type u} [Inhabited α] [Inhabited (Q α)] (q : Q α) : α × Q α :=
    if h : isEmpty q then panic "Empty queue" else dequeue q h

/--
Queue types are inhabited.
-/
public instance (priority := low) instInhabitedQueue.{u, v} {Q : Type u → Type v} [Queue Q] {α : Type u} : Inhabited (Q α) where
  default := Queue.empty

/--
Queue types are nonempty.
-/
public instance (priority := low) instNonemptyQueue.{u, v} {Q : Type u → Type v} [Queue Q] {α : Type u} : Nonempty (Q α) :=
  inferInstance

/--
Every queue should be a functor.
However, implementations should have a better way to define a `Functor` instace, so this instance is low priority.
-/
public instance (priority := low) instFunctorQueue.{u, v} {Q : Type u → Type v} [Queue Q] : Functor Q where
  map {α β : Type u} (f : α → β) :=
    let rec go (qa : Q α) (qb : Q β) : Q β :=
      if h : Queue.isEmpty qa then
        qb
      else
        let (a, qa') := Queue.dequeue qa h
        go qa' $ Queue.enqueue (f a) qb
      partial_fixpoint
    (go · Queue.empty)

end Lean4Gists.Data

