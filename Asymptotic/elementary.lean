import Asymptotic.majorize

lemma floor_eqPlusBigO {x: ℝ} (hx: 0 ≤ x) : Nat.floor x =[1] x + O(1) := by
  simp
