/-
Copyright (c) 2025 ChemistMikeLam. All rights reserved.
Released under GNU General Public License version 3.0 or later.
See file LICENSE for a copy of the license.

Authors:
- ChemistMikeLam <43129403+ChemistMikeLam at users dot noreply dot github dot com>
-/

module

public import Lean4Gists.Data.Queue.Class
public import Lean4Gists.Data.Queue.BiListQ

/-!
# FIFO queues

This component of the library contains FIFO queues.

## Interface

The interface can be found in `Lean4Gists.Data.Queue.Class`.

## Implementations

- `Lean4Gists.Data.Queue.BiListQ`:
  Standard implementation by 2 lists.
  O(1) enqueue, amortised O(1) dequeue.
-/

