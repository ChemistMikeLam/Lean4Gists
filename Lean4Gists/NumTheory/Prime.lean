module

public import Lean4Gists.NumTheory.Div

namespace Lean4Gists
namespace NumTheory

public structure Prime (p : Nat) : Prop where
  intro ::
  gto : p > 1 := by decide
  proof (n : Nat) (_ : 1 < n := by decide) (_ : n < p := by decide) (hnd : Div n p) : False

namespace Prime

public theorem two_prime : Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro
  | 0 | 1 | _ + 2 => intros; contradiction

public theorem three_prime : Prime 3 := by
  refine ⟨by decide, ?_⟩
  intro
  | 0 | 1 | _ + 3 => intros; contradiction
  | 2 => simp; exact Div.not_div 2 3 1

public theorem four_not_prime : ¬ Prime 4 :=
  λ ⟨_, h⟩ => h 2 (hnd := ⟨⟨2, rfl⟩⟩)

public theorem five_prime : Prime 5 := by
  refine ⟨by decide, ?_⟩
  intro
  | 0 | 1 | _ + 5 => intros; contradiction
  | n@h : 2 | n@h : 3 | n@h : 4 =>
    simp
    have h1 := Div.not_div n 5 (5/n) (by simp [h]) (by simp [h])
    rw [h] at h1
    exact h1

end Prime
end NumTheory
end Lean4Gists

