namespace NumTheory

structure Div (x y : Nat) : Prop where
  intro ::
  proof : ∃ (k : Nat), x * k = y

structure Prime (p : Nat) : Prop where
  intro ::
  gto : p > 1 := by decide
  proof (n : Nat) (_ : 1 < n := by decide) (_ : n < p := by decide) (hnd : Div n p) : False

theorem one_div_any {x : Nat} : Div 1 x :=
  ⟨⟨x, Nat.one_mul x⟩⟩

theorem any_div_zero {x : Nat} : Div x 0 :=
  ⟨⟨0, Nat.mul_zero x⟩⟩

theorem div_trans {x y z : Nat} : Div x y → Div y z → Div x z := by
  intro ⟨⟨kxy, hxy⟩⟩ ⟨⟨kyz, hyz⟩⟩
  refine ⟨⟨kxy * kyz, ?_⟩⟩
  rw [← Nat.mul_assoc, hxy, hyz]

instance : Trans Div Div Div where
  trans := div_trans

theorem not_div (a b x : Nat) (hs : b > a * x := by decide) (hl : b < a * (x + 1) := by decide) : ¬Div a b := by
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

theorem two_prime : Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro
  | 0 | 1 | _ + 2 => intros; contradiction

theorem three_prime : Prime 3 := by
  refine ⟨by decide, ?_⟩
  intro
  | 0 | 1 | _ + 3 => intros; contradiction
  | 2 => simp; exact not_div 2 3 1

theorem four_not_prime : ¬ Prime 4 :=
  λ ⟨_, h⟩ => h 2 (hnd := ⟨⟨2, rfl⟩⟩)

theorem five_prime : Prime 5 := by
  refine ⟨by decide, ?_⟩
  intro
  | 0 | 1 | _ + 5 => intros; contradiction
  | n@h : 2 | n@h : 3 | n@h : 4 =>
    simp
    have h1 := not_div n 5 (5/n) (by simp [h]) (by simp [h])
    rw [h] at h1
    exact h1

end NumTheory
