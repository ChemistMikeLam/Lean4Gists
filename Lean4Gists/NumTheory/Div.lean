/-
Copyright (c) 2025 ChemistMikeLam. All rights reserved.
Released under GNU General Public License version 3.0 or later.
See file LICENSE for a copy of the license.

Authors:
- ChemistMikeLam <43129403+ChemistMikeLam at users dot noreply dot github dot com>
-/

module

/-!
# Divisibility of Nats

This module contains defs and theorems about the divisibility of Nats.

The main definition in this module is the structure `Lean4Gists.NumTheory.Div`.
It carries the proof of existence of a Nat which is the quotient.

We also proves several handy theorems about divisibility that would help in proofs.
Of special note is a helper theorem (`Lean4Gists.NumTheory.Div.not_div`) which states that if the multiples of `a` "skips over" `b` then `b` is not divisible by `a`.
-/

namespace Lean4Gists.NumTheory

/--
`Div a b` means that `a` divides `b`, i.e. there exists a Nat `k` such that `a * k = b`.
-/
public structure Div (x y : Nat) : Prop where
  /--
  Takes a proof of existence of the quotient `k` to show the divisibility.
  -/
  public intro ::
  /--
  The proof of existence of the quotient.
  -/
  public proof : ∃ (k : Nat), x * k = y

namespace Div

/-!
### Basic lemmas
-/

/--
1 divides every Nat.
-/
public theorem one_div_any {x : Nat} : Div 1 x :=
  ⟨⟨x, Nat.one_mul x⟩⟩

/--
Every Nat divides 0.
-/
public theorem any_div_zero {x : Nat} : Div x 0 :=
  ⟨⟨0, Nat.mul_zero x⟩⟩

/-!
### Transitivity of `Div`
-/

/--
Divisibility is transitive.
-/
public theorem div_trans {x y z : Nat} : Div x y → Div y z → Div x z := by
  intro ⟨⟨kxy, hxy⟩⟩ ⟨⟨kyz, hyz⟩⟩
  refine ⟨⟨kxy * kyz, ?_⟩⟩
  rw [← Nat.mul_assoc, hxy, hyz]

/--
Instance to allow one to `calc` divisibility proofs.
Uses `Lean4Gists.NumTheory.Div.div_trans`.
-/
public instance : Trans Div Div Div where
  trans := div_trans

/-!
### Helper to prove *not* divisible
-/

/--
If the multiples of `a` "skips over" `b`, then `a` cannot divide `b`.

Parameters:
- `a`:
  Divisor
- `b`:
  Dividend
- `x`:
  Floor of quotient
- `hs` (auto):
  Proof that `a * x` is `s`maller than `b`
- `hl` (auto):
  Proof that `a * (x + 1)` is `l`arger than `b`
-/
public theorem not_div (a b x : Nat) (hs : b > a * x := by decide) (hl : b < a * (x + 1) := by decide) : ¬Div a b := by
  intro ⟨⟨k, hk⟩⟩
  by_cases h : k ≥ x + 1
  case pos =>
    have cont : b < b := calc
      b < a * (x + 1) := hl
      _ ≤ a * k := Nat.mul_le_mul_left a h
      _ = b := hk
    exact Nat.lt_irrefl b cont
  case neg =>
    have h' : k ≤ x := Nat.le_iff_lt_add_one.mpr $ Nat.not_le.mp h
    have cont : b < b := calc
      b = a * k := hk.symm
      _ ≤ a * x := Nat.mul_le_mul_left a h'
      _ < b := hs
    exact Nat.lt_irrefl b cont

end Lean4Gists.NumTheory.Div

