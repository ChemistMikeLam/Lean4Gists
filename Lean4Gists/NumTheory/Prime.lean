/-
Copyright (c) 2025 ChemistMikeLam. All rights reserved.
Released under GNU General Public License version 3.0 or later.
See file LICENSE for a copy of the license.

Authors:
- ChemistMikeLam <43129403+ChemistMikeLam at users dot noreply dot github dot com>
-/

module

public import Lean4Gists.NumTheory.Div

/-!
# Prime numbers

This module contains defs and theorems about prime numbers.

The main definition in this module is the structure `Lean4Gists.NumTheory.Prime`.
It carries the proof of primality of the Nat.

We also proves the primailty or non-primailty of Nats between 2 and 10 inclusive.
-/

namespace Lean4Gists.NumTheory

/--
`Prime p` is the proposition that `p` is a prime.
-/
public structure Prime (p : Nat) : Prop where
  /--
  Constructor.
  -/
  public intro ::
  /--
  A prime must be greater than 1.
  -/
  gto : p > 1 := by decide
  /--
  Proof that forall Nat `n` that `1 < n < p`, `n` cannot divide `p`.
  (In other words, `n` is not a divisor of `p`.)

  This formuation makes proofs tedius for large `p`, but is simple to understand and without much dependencies.
  -/
  proof (n : Nat) (_ : 1 < n := by decide) (_ : n < p := by decide) (hnd : Div n p) : False

namespace Prime

/-!
### Proofs of primailty or non-primality
-/

/--
2 is a prime.
-/
public theorem two_prime : Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro
  | 0 | 1 | _ + 2 => simp +arith

/--
3 is a prime.
-/
public theorem three_prime : Prime 3 := by
  refine ⟨by decide, ?_⟩
  intro
  | 0 | 1 | _ + 3 => simp +arith
  | 2 => simp; exact Div.not_div 2 3 1

/--
4 is not a prime.
-/
public theorem four_not_prime : ¬ Prime 4 :=
  λ ⟨_, h⟩ => h 2 (hnd := ⟨⟨2, rfl⟩⟩)

/--
5 is a prime.
-/
public theorem five_prime : Prime 5 := by
  refine ⟨by decide, ?_⟩
  intro
  | 0 | 1 | _ + 5 => simp +arith
  | n@h : 2 | n@h : 3 | n@h : 4 =>
    have h1 := Div.not_div n 5 (5/n) (by simp [h]) (by simp [h])
    simpa [h] using h1

/--
6 is not a prime.
-/
public theorem six_not_prime : ¬ Prime 6 :=
  λ ⟨_, h⟩ => h 2 (hnd := ⟨⟨3, rfl⟩⟩)

/--
7 is a prime.
-/
public theorem seven_prime : Prime 7 := by
  refine ⟨by decide, ?_⟩
  intro
  | 0 | 1 | _ + 7 => simp +arith
  | n@h : 2 | n@h : 3 | n@h : 4 | n@h : 5 | n@h : 6 =>
    have h1 := Div.not_div n 7 (7/n) (by simp [h]) (by simp [h])
    simpa [h] using h1

/--
8 is not a prime.
-/
public theorem eight_not_prime : ¬ Prime 8 :=
  λ ⟨_, h⟩ => h 2 (hnd := ⟨⟨4, rfl⟩⟩)

/--
9 is not a prime.
-/
public theorem nine_not_prime : ¬ Prime 9 :=
  λ ⟨_, h⟩ => h 3 (hnd := ⟨⟨3, rfl⟩⟩)

/--
10 is not a prime.
-/
public theorem ten_not_prime : ¬ Prime 10 :=
  λ ⟨_, h⟩ => h 2 (hnd := ⟨⟨5, rfl⟩⟩)

end Lean4Gists.NumTheory.Prime

