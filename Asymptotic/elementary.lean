import Asymptotic.majorize

lemma floor_eqPlusBigO {x: ℝ} (hx: 0 ≤ x) : Nat.floor x =[1] x + O(1) := by
  simp [abs_le]
  have := Nat.floor_eq_iff (n := ⌊x⌋₊) hx
  simp at this
  rcases this with ⟨h₁, h₂⟩
  constructor <;> linarith

