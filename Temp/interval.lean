import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Order.MinMax


lemma sSup_eq {A: Set ℝ} (x:ℝ) (hA: Set.Nonempty A) (h: IsLUB A x) : x = sSup A := IsLUB.unique h (Real.isLUB_sSup A hA (IsLUB.bddAbove h))

lemma nat_le_ENNReal {a:ℕ} {b:ℝ} (h: 0 ≤ b) (h': a ≤ ENNReal.ofReal b) : a ≤ b := by
  let _b: NNReal := { val := b, property := h }
  replace h' : ((a:NNReal):ENNReal) ≤ (_b:ENNReal) := by
    convert (ENNReal.ofReal_eq_coe_nnreal h) ▸ h'
  norm_cast at h'

lemma interval_count {a b: ℝ} (h: a ≤ b) (I: Set ℝ) (hI: I = Set.Ioo a b ∨ I = Set.Ioc a b ∨ I = Set.Ico a b ∨ I = Set.Icc a b) : Nat.card (I ∩ (Set.range fun (n:ℤ) ↦ (n:ℝ)) : Set ℝ) =[1] b-a + O(1) := by
  set Z := Set.range fun (n:ℤ) ↦ (n:ℝ)
  set A := I ∩ Z
  set n₀ := sInf A
  set n₁ := sSup A
  have _hA: Countable A := by
    apply Set.Countable.to_subtype (Set.Countable.mono _    (Set.countable_range (fun (n:ℤ) ↦ (n:ℝ))))
    simp
  have h_connected : Set.OrdConnected I := by
    rcases hI with rfl | rfl | rfl | rfl
    . exact Set.ordConnected_Ioo
    . exact Set.ordConnected_Ioc
    . exact Set.ordConnected_Ico
    exact Set.ordConnected_Icc
  have h_measure : MeasureTheory.volume I = ENNReal.ofReal (b - a) := by
    rcases hI with rfl | rfl | rfl | rfl
    . exact Real.volume_Ioo
    . exact Real.volume_Ioc
    . exact Real.volume_Ico
    exact Real.volume_Icc
  have h_bddAbove : BddAbove I := by
    rcases hI with rfl | rfl | rfl | rfl
    . exact bddAbove_Ioo
    . exact bddAbove_Ioc
    . exact bddAbove_Ico
    exact bddAbove_Icc
  have h_bddBelow : BddBelow I := by
    rcases hI with rfl | rfl | rfl | rfl
    . exact bddBelow_Ioo
    . exact bddBelow_Ioc
    . exact bddBelow_Ico
    exact bddBelow_Icc

  rw [Asymptotics.eqPlusBigO_iff_le_and_ge, mul_one]
  constructor
  . set A' := A \ {n₁}
    have _hA' : Countable A' := Set.Countable.to_subtype (Set.Countable.mono (Set.diff_subset A {n₁}) A.to_countable)
    have : ⋃ n ∈ A', Set.Ico (n:ℝ) (n+1) ⊆ I := by
      simp
      intro x hx n hn hn'
      have : x+1 ∈ I := by
        contrapose! hn'
        apply sSup_eq
        . use x
          simp [hx]
          exact ⟨ n, hn ⟩
        apply IsGreatest.isLUB
        rw [IsGreatest]
        constructor
        . simp [hx]
          exact ⟨ n, hn ⟩
        simp [upperBounds]
        intro y hy m hm
        contrapose! hn'
        have : x+1 ∈ Set.Icc x y := by
          simp [<-hn, <-hm] at hn' ⊢
          norm_cast at hn' ⊢
        exact Set.OrdConnected.out h_connected hx hy this
      exact subset_trans Set.Ico_subset_Icc_self (Set.OrdConnected.out h_connected hx this)
    replace this := MeasureTheory.measure_mono (μ := MeasureTheory.volume) this
    rw [h_measure, MeasureTheory.measure_biUnion] at this
    . simp [Real.volume_Ico, ENNReal.tsum_const_eq] at this
      have hf := (MeasureTheory.Measure.count_apply_lt_top' MeasurableSet.univ).mp (lt_of_le_of_lt this ENNReal.ofReal_lt_top)
      have hf': Fintype A' := @Fintype.ofFinite A' (Finite.of_finite_univ hf)
      rw [MeasureTheory.Measure.count_apply_finite _ hf, Set.Finite.toFinset_univ hf, Finset.card_univ, <-Nat.card_eq_fintype_card] at this
      norm_cast at this
      replace this := nat_le_ENNReal (by linarith) this
      have h : A ⊆ A' ∪ {n₁} := by simp
      rw [Set.Nat.card_coe_set_eq] at this ⊢
      rw [<- tsub_le_iff_right]
      have h' : Set.ncard A - (1:ℝ) ≤ (Set.ncard A - 1:ℕ) := by
        rw [tsub_le_iff_right]
        norm_cast
        exact le_tsub_add
      apply h'.trans (LE.le.trans _ this)
      norm_cast
      exact Set.pred_ncard_le_ncard_diff_singleton A n₁
    . exact Set.Countable.mono (Set.diff_subset _ _) A.to_countable
    . by_contra h
      replace h := Set.exists_lt_mem_inter_of_not_pairwiseDisjoint h
      rcases h with ⟨ x, hx, y, hy, ⟨ hxy, ⟨ z, hz ⟩ ⟩ ⟩
      simp at hz
      replace hz := lt_of_le_of_lt hz.2.1 hz.1.2
      simp at hx hy
      rcases hx.1.2 with ⟨n, hn⟩
      rcases hy.1.2 with ⟨m, hm⟩
      rw [← hn, ← hm] at hz hxy
      norm_cast at hz hxy
      linarith only [hz, hxy]
    intro n
    measurability
  set A' := A ∪ {n₀-1}
  have _hA' : Countable A' := Set.Countable.to_subtype (Set.countable_union.mpr ⟨ A.to_countable, Set.countable_singleton _⟩)
  have : I ⊆ ⋃ n ∈ A', Set.Ico (n:ℝ) (n+1) := by
    sorry
  sorry
