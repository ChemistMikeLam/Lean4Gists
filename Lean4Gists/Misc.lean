/-
Copyright (c) 2025 ChemistMikeLam. All rights reserved.
Released under GNU General Public License version 3.0 or later.
See file LICENSE for a copy of the license.

Authors:
- ChemistMikeLam <43129403+ChemistMikeLam at users dot noreply dot github dot com>
-/

module

/-!
# Miscellaneous

This module contains all the defs, theorems, etc that does not fit in any other modules.

Other modules, except the root module, are not expected to import this module.
If a def is expected to be reused in other modules, it should live in `Utils.lean`.
-/

namespace Lean4Gists.Misc

/--
The Ackermann function.
Implemented to test the termination-checking ability of lean.
-/
public def ackermann : Nat → Nat → Nat
  | 0, n => n + 1
  | (m + 1), 0 => ackermann m 1
  | (m + 1), (n + 1) => ackermann m $ ackermann (m + 1) n

end Lean4Gists.Misc

