/-
Copyright (c) 2025 ChemistMikeLam. All rights reserved.
Released under GNU General Public License version 3.0 or later.
See file LICENSE for a copy of the license.

Authors:
- ChemistMikeLam <43129403+ChemistMikeLam at users dot noreply dot github dot com>
-/

module

public import Lean4Gists.Util.Vec.Basic

/-!
# Length-indexed vectors

This part of the library contains various utilities concerning `Lean4Gists.Util.Vec`,
a length-indexed vector type.

Definitions of the type, along with major functions, are available in submodule `Lean4Gists.Util.Vec.Basic`.
If you only need those functions for programming, you should consider importing that submodule only.

This module additionally imports lemmas in `Lean4Gists.Util.Vec.Lemma`.
If you want to prove theorems about `Vec`s, you might want to directly import this file.
-/

