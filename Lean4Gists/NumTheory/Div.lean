module

namespace Lean4Gists
namespace NumTheory

public structure Div (x y : Nat) : Prop where
  intro ::
  proof : ∃ (k : Nat), x * k = y

namespace Div

public theorem one_div_any {x : Nat} : Div 1 x :=
  ⟨⟨x, Nat.one_mul x⟩⟩

public theorem any_div_zero {x : Nat} : Div x 0 :=
  ⟨⟨0, Nat.mul_zero x⟩⟩

public theorem div_trans {x y z : Nat} : Div x y → Div y z → Div x z := by
  intro ⟨⟨kxy, hxy⟩⟩ ⟨⟨kyz, hyz⟩⟩
  refine ⟨⟨kxy * kyz, ?_⟩⟩
  rw [← Nat.mul_assoc, hxy, hyz]

public instance : Trans Div Div Div where
  trans := div_trans

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

end Div
end NumTheory
end Lean4Gists

