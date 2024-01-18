import Asymptotic.majorize
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Data.Set.Intervals.OrdConnected

lemma Nat.floor_eqPlusBigO {x: ℝ} (hx: 0 ≤ x) : ⌊x⌋₊ =[1] x + O(1) := by
  simp [abs_le]
  have := Nat.floor_eq_iff (n := ⌊x⌋₊) hx
  simp at this
  rcases this with ⟨h₁, h₂⟩
  constructor <;> linarith

lemma Nat.ceil_eqPlusBigO {x: ℝ} (hx: 0 ≤ x) : ⌈x⌉₊ =[1] x + O(1) := by
  simp [abs_le]
  constructor
  . linarith only [Nat.le_ceil x]
  have : ⌈x⌉₊ ≤ ⌊x⌋₊ + (1:ℝ) := by norm_cast; exact ceil_le_floor_add_one x
  linarith only [this, Nat.floor_le hx]

lemma Int.floor_eqPlusBigO {x: ℝ} : ⌊x⌋ =[1] x + O(1) := by
  simp [abs_le]
  constructor
  . linarith only [Int.lt_floor_add_one x]
  linarith only [Int.floor_le x]

lemma Int.ceil_eqPlusBigO {x: ℝ} : ⌈x⌉ =[1] x + O(1) := by
  simp [abs_le]
  constructor
  . linarith only [Int.le_ceil x]
  linarith only [Int.ceil_lt_add_one x]

lemma Int.floor_plus_one_eqPlusBigO {x: ℝ} : ⌊x⌋+1 =[1] x + O(1) := by
  simp [abs_le]
  constructor
  . linarith only [Int.lt_floor_add_one x]
  linarith only [Int.floor_le x]

lemma Int.ceil_sub_one_eqPlusBigO {x: ℝ} : ⌈x⌉-1 =[1] x + O(1) := by
  simp [abs_le]
  constructor
  . linarith only [Int.le_ceil x]
  linarith only [Int.ceil_lt_add_one x]

lemma coe_of_sub_of_nat_eq (a b: ℕ) : (a-b:ℕ) = max 0 (a-b:ℝ) := by
  norm_cast
  rw [Int.subNatNat_eq_coe, max_def]
  split <;>
  omega

lemma coe_of_int_toNat_eq  (a:ℤ) : Int.toNat a = max (0:ℝ) a := by
  norm_cast
  rw [max_comm]
  exact Int.toNat_eq_max a

def ℤᵣ : Set ℝ := Set.range fun (n:ℤ) ↦ (n:ℝ)

lemma interval_count {a b: ℝ} (h: a ≤ b) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : Nat.card (I ∩ ℤᵣ : Set ℝ) =[1] b-a + O(1) := by
  set ι := fun (n:ℤ) ↦ (n:ℝ)
  rw [Asymptotics.eqPlusBigO_iff_le_and_ge, mul_one]
  have hi : I ∩ ℤᵣ ⊆ ι '' (Set.Ioo (⌈a⌉-1) (⌊b⌋+1)) := by
    intro x hx
    simp at hx ⊢
    rcases hx.2 with ⟨n, rfl⟩
    refine ⟨ n, ⟨ ?_, rfl ⟩ ⟩
    replace hx := hI' hx.1
    simp at hx
    constructor
    . replace hx := lt_of_lt_of_le (sub_lt_iff_lt_add.mpr (Int.ceil_lt_add_one a)) hx.1
      norm_cast at hx
    replace hx := lt_of_le_of_lt hx.2 (Int.lt_floor_add_one b)
    norm_cast at hx
  have hfin' : Set.Finite (ι '' (Set.Ioo (⌈a⌉-1) (⌊b⌋+1))) := Set.Finite.image _ (Set.finite_Ioo _ _)
  have hfin : Set.Finite (I ∩ ℤᵣ) := Set.Finite.subset hfin' hi
  constructor
  . apply (Nat.cast_le.mpr (Nat.card_mono hfin' hi)).trans
    rw [Nat.card_image_of_injective Int.cast_injective _]
    simp
    rw [coe_of_sub_of_nat_eq, max_le_iff]
    constructor
    . linarith only [h]
    rw [sub_le_iff_le_add, coe_of_int_toNat_eq , max_le_iff]
    constructor
    . linarith only [h]
    push_cast
    linarith only [Int.floor_le b, Int.le_ceil a]
  have : ι '' (Set.Icc (⌊a⌋+1) (⌈b⌉-1)) ⊆ I := by
     apply subset_trans _ hI
     simp
     intro n hn
     simp at hn ⊢
     exact ⟨ by linarith only [hn.1], by linarith only [hn.2] ⟩
  replace this : ι '' Set.Icc (⌊a⌋ + 1) (⌈b⌉ - 1) ⊆ I ∩ ℤᵣ := Set.subset_inter this (Set.image_subset_range _ _)
  apply LE.le.trans _ (Nat.cast_le.mpr (Nat.card_mono hfin this))
  rw [Nat.card_image_of_injective Int.cast_injective _]
  simp [coe_of_int_toNat_eq ]
  right
  linarith only [Int.floor_le a, Int.le_ceil b]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

open BigOperators MeasureTheory

lemma ftoc {a b c:ℝ} (f: ℝ → E) (hderiv: ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (hcont': ContinuousOn (deriv f) (Set.Icc a b))
 (hc: c ∈ Set.Icc a b) : ∀ x ∈ Set.Icc a b, f x = f c + ∫ t in Set.Icc a b, (if t ≥ c then (if x ≥ t then 1 else 0) else -(if x ≤ t then 1 else 0)) • deriv f t ∂ volume := by
  intro x hx
  simp at hc
  rcases le_or_gt c x with h | h
  . simp [h]
    rw [set_integral_eq_of_subset_of_ae_diff_eq_zero (s := Set.Ioc c x)]
    . rw [set_integral_congr (g := deriv f)]
      . rw [<- intervalIntegral.integral_of_le h, intervalIntegral.integral_deriv_eq_sub' f (by rfl) _ _]
        . abel
        . intro t ht
          apply hderiv t
          simp [h] at ht hx ⊢
          exact ⟨ hc.1.trans ht.1, ht.2.trans hx.2⟩
        apply ContinuousOn.mono hcont'
        intro t ht
        simp [h] at ht hx ⊢
        exact ⟨ hc.1.trans ht.1, ht.2.trans hx.2 ⟩
      . exact measurableSet_Ioc
      intro t ht
      simp at ht
      simp [LT.lt.le ht.1, ht.2]
    . exact MeasurableSet.nullMeasurableSet measurableSet_Icc
    . simp at hx
      intro t; simp
      intro h1 h2; exact ⟨ by linarith only [hc.1, h1], by linarith only [hx.2, h2] ⟩
    rw [ae_iff, measure_mono_null (s₂ := {c} ∪ {x})]
    . intro t ht
      simp at ht ⊢
      by_cases h' : c ≤ t
      . simp [h'] at ht
        rcases le_iff_lt_or_eq.mp h' with h' | h'
        . exact Or.inl (by linarith only [ht.1 h', ht.2.2.2.1])
        exact Or.inr h'.symm
      simp [h'] at ht
      contrapose! h'
      exact h.trans ht.2.2.2.1
    exact measure_union_null Real.volume_singleton Real.volume_singleton
  simp [h]
  rw [set_integral_eq_of_subset_of_ae_diff_eq_zero (s := Set.Ioc x c)]
  . rw [set_integral_congr_ae (g := -deriv f)]
    . change f x = f c + ∫ (x : ℝ) in Set.Ioc x c, - (deriv f x)
      rw [MeasureTheory.integral_neg, <- intervalIntegral.integral_of_le (LT.lt.le h), intervalIntegral.integral_deriv_eq_sub' f (by rfl) _ _]
      . abel
      . intro t ht
        apply hderiv t
        simp [LT.lt.le h] at ht hx ⊢
        exact ⟨ hx.1.trans ht.1, ht.2.trans hc.2 ⟩
      apply ContinuousOn.mono hcont'
      intro t ht
      simp [LT.lt.le h] at ht hx ⊢
      exact ⟨ hx.1.trans ht.1, ht.2.trans hc.2 ⟩
    . exact measurableSet_Ioc
    rw [ae_iff, measure_mono_null (s₂ := {c})]
    . intro t ht
      simp at ht ⊢
      rcases le_iff_lt_or_eq.mp ht.1 with h' | h'
      . simp [not_le.mpr h'] at ht
        linarith [ht.2.1, ht.2.2.1]
      exact h'
    exact Real.volume_singleton
  . exact MeasurableSet.nullMeasurableSet measurableSet_Icc
  . simp at hx
    intro t; simp
    intro h1 h2; exact ⟨ by linarith only [hx.1, h1], h2.trans hc.2 ⟩
  rw [ae_iff, measure_mono_null (s₂ := {c} ∪ {x})]
  . intro t ht
    simp at ht ⊢
    by_cases h' : c ≤ t
    . simp [h'] at ht
      rcases le_iff_lt_or_eq.mp h' with h' | h'
      . linarith only [h', ht.2.2.2.1, h]
      exact Or.inr h'.symm
    simp [h'] at ht
    contrapose! h'
    exact LT.lt.le (ht.1 ((Ne.le_iff_lt h'.1.symm).mp ht.2.2.2.1))
  exact measure_union_null Real.volume_singleton Real.volume_singleton


open Classical Asymptotics

noncomputable def discretize (I: Set ℝ) : Finset ℤ := if h : Set.Finite {n:ℤ | (n:ℝ) ∈ I } then h.toFinset else ∅

lemma finite_of_bounded {I: Set ℤ} (hu: BddAbove I) (hl: BddBelow I) : Set.Finite I := by
  rw [bddAbove_def] at hu
  rw [bddBelow_def] at hl
  rcases hu with ⟨ b, hb ⟩
  rcases hl with ⟨ a, ha ⟩
  apply Set.Finite.subset (Set.finite_Icc a b) _
  intro y hy
  simp [ha y hy, hb y hy]

lemma discretize_finite {I: Set ℝ} (hu: BddAbove I) (hl: BddBelow I) : Set.Finite {n:ℤ | (n:ℝ) ∈ I } := by
  apply finite_of_bounded
  . rw [bddAbove_def] at hu ⊢
    rcases hu with ⟨ x, hx ⟩
    use ⌈ x ⌉
    intro n hn
    simp at hn
    replace hn := (hx n hn).trans (Int.le_ceil x)
    norm_cast at hn
  rw [bddBelow_def] at hl ⊢
  rcases hl with ⟨ x, hx ⟩
  use ⌊ x ⌋
  intro n hn
  simp at hn
  replace hn := (Int.floor_le x).trans (hx n hn)
  norm_cast at hn

lemma discretize_mem {I: Set ℝ} (hu: BddAbove I) (hl: BddBelow I) (n:ℤ) : n ∈ discretize I ↔ (n:ℝ) ∈ I := by
  have := discretize_finite hu hl
  simp [discretize, this]

lemma unit_interval_subset_or_inf {I : Set ℝ} [hI: Set.OrdConnected I]  (hu: BddAbove I) (hl: BddBelow I) {n : ℤ} (hn: n ∈ discretize I) (hsub: ¬ Set.Icc ((n:ℝ)-1) (n:ℝ) ⊆ I) : IsLeast (discretize I) n := by
  rcases Set.not_subset.mp hsub with ⟨ x, ⟨ hx1, hx2 ⟩ ⟩
  simp at hx1
  simp [IsLeast]
  refine ⟨ hn, ?_ ⟩
  simp [lowerBounds]
  intro m hm
  contrapose! hx2
  have sub : Set.Icc (m:ℝ) (n:ℝ) ⊆ I := by
    apply Set.OrdConnected.out hI
    . exact (discretize_mem hu hl m).mp hm
    exact (discretize_mem hu hl n).mp hn
  apply sub
  have : (m:ℝ) ≤ (n:ℝ)-1 := by norm_cast; linarith only [hx2]
  simp; refine ⟨ this.trans ?_, hx1.2 ⟩; linarith only [hx1.1]

example (A B : Prop) (h: ¬A → B) : A ∨ B := by exact or_iff_not_imp_left.mpr h

lemma unit_interval_cover {I : Set ℝ} [hI: Set.OrdConnected I]  (hu: BddAbove I) (hl: BddBelow I) {a : ℝ} (ha: IsGLB I a) : I ⊆ (Set.Ico a (a+1)) ∪ ⋃ n ∈ discretize I, Set.Ico (n:ℝ) (n+1) := by
  intro x hx
  simp
  rw [or_iff_not_imp_left]
  intro ha'
  replace ha' : x ≥ a+1 := by
    contrapose! ha'
    exact ⟨ (Set.mem_of_mem_inter_left ha) hx, ha' ⟩
  use ⌊ x ⌋
  refine ⟨ Int.floor_le x, ?_, Int.lt_floor_add_one x ⟩
  rw [discretize_mem hu hl _]
  have : a < ⌊ x ⌋ := lt_of_le_of_lt (le_sub_iff_add_le.mpr ha') (Int.sub_one_lt_floor x)
  rcases (isGLB_lt_iff ha).mp this with ⟨ y, ⟨ hy, hy' ⟩ ⟩
  apply (Set.OrdConnected.out hI hy hx) _
  simp
  exact ⟨ le_of_lt hy', Int.floor_le x⟩

lemma sum_approx_eq_integral {a b c:ℝ} (h: a ≤ b) (f: ℝ → E)  (hderiv: ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (hcont': ContinuousOn (deriv f) (Set.Icc a b)) (hc: c ∈ Set.Icc a b) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : ∑ n in discretize I, f n =[1] ∫ t in I, f t ∂ volume + O( ‖f c‖ + ∫ t in I, ‖deriv f t‖ ∂ volume) := by
  let χ : ℝ → ℝ → ℤ := fun s ↦ fun x ↦ if s ≥ c then (if x ≥ s then 1 else 0) else -(if x ≤ s then 1 else 0)
  have repr : ∀ x ∈ Set.Icc a b, f x = f c + ∫ s in Set.Icc a b, (χ s x) • deriv f s ∂ volume := ftoc f hderiv hcont' hc
  have split_lhs : ∑ n in discretize I, f n = ∑ n in discretize I, f c + ∫ s in Set.Icc a b, ∑ n in discretize I, (χ s n) • deriv f s := by
    sorry
  have split_rhs : ∫ t in I, f t ∂ volume = ∫ t in I, f c ∂ volume + ∫ s in Set.Icc a b, (∫ t in I, (χ s t) • deriv f s ∂ volume) ∂ volume := by
    sorry
  rw [split_lhs, split_rhs]
  apply add_of_eqPlusBigO _ _
  . sorry
  sorry
