import Asymptotic.majorize

lemma floor_eqPlusBigO {x: ℝ} (hx: 0 ≤ x) : Nat.floor x =[1] x + O(1) := by
  simp [abs_le]
  have := Nat.floor_eq_iff (n := ⌊x⌋₊) hx
  simp at this
  rcases this with ⟨h₁, h₂⟩
  constructor <;> linarith

lemma interval_count {a b: ℝ} (h: a ≤ b) (I: Set ℝ) (hI: I = Set.Ioo a b ∨ I = Set.Ioc a b ∨ I = Set.Ico a b ∨ I = Set.Icc a b) : Nat.card (I ∩ (Set.range fun (n:ℤ) ↦ (n:ℝ)) : Set ℝ) =[1] b-a + O(1) := by
  set Z := Set.range fun (n:ℤ) ↦ (n:ℝ)
  set A := Z ∩ I
  -- show that I contains [n,n+1] for all n in A that are not the greatest element
  -- show that I is contained in the union of [n,n+1] for all n in A, or one less than the least element
  sorry

-- show that  sum_{n in I cap Z} f =[1] int_I f + O(|| f ||_TV); approximate the TV function uniformly by a step function and use previous lemma
