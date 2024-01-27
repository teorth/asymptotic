import Asymptotic.majorize
import Asymptotic.discretize
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Data.Set.Intervals.OrdConnected
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Init.Data.Int.CompLemmas

-- Tools for comparing a sum with an integral.


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

@[simp]
lemma coe_of_int_toNat_eq  (a:ℤ) : Int.toNat a = max (0:ℤ) a := by
  norm_cast
  rw [max_comm]
  exact Int.toNat_eq_max a

@[simp]
lemma coe_of_int_toNat_eq'  (a:ℤ) : Int.toNat a = max (0:ℝ) a := by
  norm_cast
  rw [max_comm]
  exact Int.toNat_eq_max a

lemma interval_count {a b: ℝ} (h: a ≤ b) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : Finset.card I.discretize =[1] b-a + O(1) := by
  rw [Asymptotics.eqPlusBigO_iff_le_and_ge, mul_one]
  constructor
  . apply (Nat.cast_le.mpr (Finset.card_mono (Set.discretize_mono hI' (OrdBounded.icc a b)))).trans
    simp
    constructor
    all_goals linarith only [h, Int.le_ceil a, Int.floor_le b]
  apply le_trans _ <| Nat.cast_le.mpr  <| Finset.card_mono <| Set.discretize_mono hI <| ordBounded_of_subset_of_icc hI'
  simp [coe_of_sub_of_nat_eq]
  right; right
  linarith only [ Int.le_ceil b, Int.floor_le a]



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

@[simp]
lemma discretize_Ico {a b:ℝ}: discretize (Set.Ico a b) = Set.Ico ⌈ a ⌉ ⌈ b ⌉ := by
  ext n
  simp [discretize_mem bddAbove_Ico bddBelow_Ico n]
  constructor
  . rintro ⟨ h1, h2 ⟩
    exact ⟨ Int.ceil_le.mpr h1, Int.lt_ceil.mpr h2 ⟩
  rintro ⟨ h1, h2⟩
  exact ⟨ Int.ceil_le.mp h1, Int.lt_ceil.mp h2 ⟩

@[simp]
lemma discretize_Ioc {a b:ℝ}: discretize (Set.Ioc a b) = Set.Ioc ⌊ a ⌋ ⌊ b ⌋ := by
  ext n
  simp [discretize_mem bddAbove_Ioc bddBelow_Ioc n]
  constructor
  . rintro ⟨ h1, h2 ⟩
    exact ⟨ Int.floor_lt.mpr h1, Int.le_floor.mpr h2 ⟩
  rintro ⟨ h1, h2⟩
  exact ⟨ Int.floor_lt.mp h1, Int.le_floor.mp h2 ⟩

@[simp]
lemma discretize_Icc {a b:ℝ}: discretize (Set.Icc a b) = Set.Icc ⌈ a ⌉ ⌊ b ⌋ := by
  ext n
  simp [discretize_mem bddAbove_Icc bddBelow_Icc n]
  constructor
  . rintro ⟨ h1, h2 ⟩
    exact ⟨ Int.ceil_le.mpr h1, Int.le_floor.mpr h2 ⟩
  rintro ⟨ h1, h2⟩
  exact ⟨ Int.ceil_le.mp h1, Int.le_floor.mp h2 ⟩

@[simp]
lemma discretize_Ioo {a b:ℝ}: discretize (Set.Ioo a b) = Set.Ioo ⌊ a ⌋ ⌈ b ⌉ := by
  ext n
  simp [discretize_mem bddAbove_Ioo bddBelow_Ioo n]
  constructor
  . rintro ⟨ h1, h2 ⟩
    exact ⟨ Int.floor_lt.mpr h1, Int.lt_ceil.mpr h2 ⟩
  rintro ⟨ h1, h2⟩
  exact ⟨ Int.floor_lt.mp h1, Int.lt_ceil.mp h2 ⟩

/-- These are superseded by Nat.image_cast_int_Ico etc. in sufficiently recent versions of Mathlib -/
lemma ico_Int_ofNat_eq_Int_ofNat_ico (a b:ℕ) : Set.Ico (a:ℤ) (b:ℤ) = Nat.cast '' (Set.Ico a b):= by
  simp

lemma icc_Int_ofNat_eq_Int_ofNat_icc (a b:ℕ) : Set.Icc (a:ℤ) (b:ℤ) = Nat.cast '' (Set.Icc a b) := by
  simp

lemma ioc_Int_ofNat_eq_Int_ofNat_ioc (a b:ℕ) : Set.Ioc (a:ℤ) (b:ℤ) = Nat.cast '' (Set.Ioc a b) := by
  simp

lemma ioo_Int_ofNat_eq_Int_ofNat_ioo (a b:ℕ) : Set.Ioo (a:ℤ) (b:ℤ) = Nat.cast '' (Set.Ioo a b) := by
  simp

lemma ici_Int_ofNat_eq_Int_ofNat_ici (a:ℕ) : Set.Ici (a:ℤ) = Nat.cast '' (Set.Ici a) := by
  simp

lemma ioi_Int_ofNat_eq_Int_ofNat_ioi (a:ℕ) : Set.Ioi (a:ℤ) = Nat.cast '' (Set.Ioi a) := by
  simp

lemma discretize_Ico_nonneg {a b:ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b): discretize (Set.Ico a b) = (Nat.cast : ℕ → ℤ) '' (Set.Ico ⌈ a ⌉₊ ⌈ b ⌉₊) := by
  rw [discretize_Ico, <-ico_Int_ofNat_eq_Int_ofNat_ico, Nat.cast_ceil_eq_int_ceil ha, Nat.cast_ceil_eq_int_ceil hb]

  lemma discretize_Icc_nonneg {a b:ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b): discretize (Set.Icc a b) = (Nat.cast : ℕ → ℤ) '' (Set.Icc ⌈ a ⌉₊ ⌊ b ⌋₊) := by
  rw [discretize_Icc, <-icc_Int_ofNat_eq_Int_ofNat_icc, Nat.cast_ceil_eq_int_ceil ha, Nat.cast_floor_eq_int_floor hb]

lemma discretize_Ioc_nonneg {a b:ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b): discretize (Set.Ioc a b) = (Nat.cast : ℕ → ℤ) '' (Set.Ioc ⌊ a ⌋₊ ⌊ b ⌋₊) := by
  rw [discretize_Ioc, <-ioc_Int_ofNat_eq_Int_ofNat_ioc, Nat.cast_floor_eq_int_floor ha, Nat.cast_floor_eq_int_floor hb]

lemma discretize_Ioo_nonneg {a b:ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b): discretize (Set.Ioo a b) = (Nat.cast : ℕ → ℤ) '' (Set.Ioo ⌊ a ⌋₊ ⌈ b ⌉₊) := by
  rw [discretize_Ioo, <-ioo_Int_ofNat_eq_Int_ofNat_ioo, Nat.cast_floor_eq_int_floor ha, Nat.cast_ceil_eq_int_ceil hb]



lemma unit_interval_subset_or_inf {I : Set ℝ} [hI: Set.OrdConnected I]  (hu: BddAbove I) (hl: BddBelow I) {n : ℤ} (hn: n ∈ discretize I) (hsub: ¬ IsLeast (discretize I) n) : Set.Ico ((n:ℝ)-1) (n:ℝ) ⊆ I := by
  contrapose! hsub
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
  simp; refine ⟨ this.trans ?_, le_of_lt hx1.2 ⟩; linarith only [hx1.1]

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

lemma integ_on_biunion_le_sum_integ {Ω: Type*} [MeasurableSpace Ω] {μ: MeasureTheory.Measure Ω} {E: Set Ω} {A: Type*} {I: Finset A} {s: A → Set Ω} {f: Ω → ℝ} (hf: MeasureTheory.IntegrableOn f E μ) (hpos: ∀ x ∈ E, f x ≥ 0) (hs: ∀ i ∈ I, MeasurableSet (s i)) (hs' : ∀ i ∈ I, s i ⊆ E): ∫ x in ⋃ i ∈ I, s i, f x ∂ μ ≤ ∑ i in I, ∫ x in s i, f x ∂ μ := calc
  _ = ∫ x, Set.indicator (⋃ i ∈ I, s i) f x ∂ μ := by
    rw [<-MeasureTheory.integral_indicator]
    exact Finset.measurableSet_biUnion _ hs
  _ ≤ ∫ x, ∑ i in I, Set.indicator (s i) f x ∂ μ := by
    apply MeasureTheory.integral_mono
    . apply MeasureTheory.IntegrableOn.integrable_indicator (MeasureTheory.IntegrableOn.mono_set hf _) (Finset.measurableSet_biUnion _ hs)
      simpa
    . apply MeasureTheory.integrable_finset_sum
      intro i hi
      apply MeasureTheory.IntegrableOn.integrable_indicator (MeasureTheory.IntegrableOn.mono_set hf (hs' i hi)) (hs i hi)
    intro x
    have hpos': ∀ j ∈ I, 0 ≤ if x ∈ s j then f x else 0 := by
      intro j hj
      by_cases hjs : x ∈ s j
      . simp [hjs, hpos x ((hs' j hj) hjs)]
      simp [hjs]
    by_cases h : ∃ i ∈ I, x ∈ s i
    . simp [Set.indicator, h]
      rcases h with ⟨ i, ⟨ hi, hs ⟩ ⟩
      convert Finset.single_le_sum hpos' hi
      simp [hs]
    simp [Set.indicator, h]
    exact Finset.sum_nonneg hpos'
  _ = ∑ i in I, ∫ x, Set.indicator (s i) f x ∂ μ := by
    refine integral_finset_sum I ?_
    intro i hi
    apply MeasureTheory.IntegrableOn.integrable_indicator (MeasureTheory.IntegrableOn.mono_set hf (hs' i hi)) (hs i hi)
  _ = _ := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [MeasureTheory.integral_indicator (hs i hi)]

lemma integ_on_union_le_add_integ {Ω: Type*} [MeasurableSpace Ω] {μ: MeasureTheory.Measure Ω} {E: Set Ω} {s t: Set Ω} {f: Ω → ℝ} (hf: MeasureTheory.IntegrableOn f E μ) (hpos: ∀ x ∈ E, f x ≥ 0) (hs: MeasurableSet s) (ht: MeasurableSet t) (hs' : s ⊆ E) (ht' : t ⊆ E) : ∫ x in s ∪ t, f x ∂ μ ≤ ∫ x in s, f x ∂ μ + ∫ x in t, f x ∂ μ  := by
  have hs_integ := MeasureTheory.IntegrableOn.integrable_indicator (MeasureTheory.IntegrableOn.mono_set hf hs') hs
  have ht_integ := MeasureTheory.IntegrableOn.integrable_indicator (MeasureTheory.IntegrableOn.mono_set hf ht') ht
  rw [<-MeasureTheory.integral_indicator hs, <-MeasureTheory.integral_indicator ht, <-MeasureTheory.integral_indicator (MeasurableSet.union hs ht), <-MeasureTheory.integral_add hs_integ ht_integ]
  apply MeasureTheory.integral_mono
  . apply MeasureTheory.IntegrableOn.integrable_indicator (MeasureTheory.IntegrableOn.mono_set hf (Set.union_subset hs' ht')) (MeasurableSet.union hs ht)
  . apply MeasureTheory.Integrable.add hs_integ ht_integ
  intro x
  simp [Set.indicator]
  by_cases h: x ∈ s
  . by_cases h': x ∈ t
    . simp [h, h', hpos x (hs' h)]
    simp [h,h']
  by_cases h': x ∈ t
  . simp [h,h']
  simp [h,h']


lemma sum_approx_eq_integral_antitone {a b:ℝ} (h: a ≤ b) (f: ℝ → ℝ) (hf: AntitoneOn f (Set.Icc a b)) (hf': f b ≥ 0) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : ∑ n in discretize I, f n =[1] ∫ t in I, f t ∂ volume + O( f a ) := by
  have hu : BddAbove I := BddAbove.mono hI' bddAbove_Icc
  have hl : BddBelow I := BddBelow.mono hI' bddBelow_Icc
  have hc : Set.OrdConnected I := by
    apply Set.ordConnected_of_Ioo
    intro x hx y hy _
    apply LE.le.trans _ hI
    intro z hz
    replace hx := hI' hx
    replace hy := hI' hy
    simp at hz hx hy ⊢
    exact ⟨ lt_of_le_of_lt hx.1 hz.1, lt_of_lt_of_le hz.2 hy.2 ⟩
  have hmes: MeasurableSet I := by
    rw [<-measurableSet_insert (a := a), <-measurableSet_insert (a := b)]
    convert measurableSet_Icc (a := a) (b := b)
    ext x
    simp
    constructor
    . intro this
      rcases this with this | this | this
      . simp [this, h]
      . simp [this, h]
      exact Set.mem_Icc.mp (hI' this)
    intro this
    rcases le_iff_lt_or_eq.mp this.1 with h1 | h1
    . rcases le_iff_lt_or_eq.mp this.2 with h2 | h2
      . right; right; apply hI
        simp [h1, h2]
      simp [h2]
    simp [h1]
  have hnonneg : ∀ x ∈ Set.Icc a b, f x ≥ 0 := by
    intro x hx
    apply hf'.trans (hf hx (Set.right_mem_Icc.mpr h) (Set.mem_Icc.mp hx).2)
  have hinteg: IntegrableOn f I := by
    apply MeasureTheory.IntegrableOn.mono_set _ hI'
    rw [MeasureTheory.integrableOn_def]
    apply MeasureTheory.Integrable.mono' (g := fun _ ↦ f a)
    . simp
    . rw [aestronglyMeasurable_iff_aemeasurable]
      exact aemeasurable_restrict_of_antitoneOn measurableSet_Icc hf
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    apply Filter.eventually_of_forall
    intro x hx
    simp [abs_of_nonneg (hnonneg x hx)]
    apply hf (Set.left_mem_Icc.mpr h) hx
    simp at hx
    exact hx.1

  rw [eqPlusBigO_iff_le_and_ge]
  constructor
  . calc
      _ ≤ ∑ n in discretize I, ((∫ t in (Set.Ico ((n:ℝ)-1) (n:ℝ)) ∩ I, f t ∂ volume) + if (IsLeast (discretize I) n) then (f a) else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hmin : IsLeast (discretize I) n
        . simp [hmin]
          rw [discretize_mem hu hl] at hn
          apply (hf (Set.left_mem_Icc.mpr h) (hI' hn) ((Set.mem_Icc.mp (hI' hn)).1)).trans
          rw [le_add_iff_nonneg_left]
          apply MeasureTheory.set_integral_nonneg (MeasurableSet.inter measurableSet_Ico hmes)
          intro x hx
          simp at hx
          exact hnonneg x (hI' hx.2)
        simp [hmin]
        replace hmin := unit_interval_subset_or_inf hu hl hn hmin
        rw [Set.inter_eq_left.mpr hmin]
        calc
          _ = ∫ _ in Set.Ico ((n:ℝ)-1) (n:ℝ), f n ∂ volume := by
            simp
          _ ≤ _ := by
            apply MeasureTheory.set_integral_mono_on _ _ measurableSet_Ico _
            . simp
            . exact MeasureTheory.IntegrableOn.mono_set hinteg hmin
            intro x hx
            exact hf (hI' (hmin hx)) (hI' ((discretize_mem hu hl n).mp hn)) (le_of_lt hx.2)
      _ ≤ ∑ n in discretize I, (∫ t in (Set.Ico ((n:ℝ)-1) (n:ℝ)) ∩ I, f t ∂ volume) + f a := by
        rw [Finset.sum_add_distrib, add_le_add_iff_left, Finset.sum_ite]
        simp
        apply mul_le_of_le_one_left (hnonneg a (Set.left_mem_Icc.mpr h)) _
        norm_cast
        rw [Finset.card_le_one]
        intro a ha b hb
        simp at ha hb
        exact IsLeast.unique ha.2 hb.2
      _ ≤ ∫ t in I, f t ∂ volume + f a := by
        rw [add_le_add_iff_right]
        calc
          _ = ∫ t in ⋃ n ∈ discretize I, (Set.Ico ((n:ℝ)-1) (n:ℝ) ∩ I), f t ∂ volume := by
            apply (MeasureTheory.integral_finset_biUnion _ _ _ _).symm
            . intro n _
              exact MeasurableSet.inter measurableSet_Ico hmes
            . apply Pairwise.set_pairwise
              rw [pairwise_disjoint_on]
              intro m n hmn
              by_contra h
              rw [Set.not_disjoint_iff] at h
              rcases h with ⟨ x, hx, hx' ⟩
              simp at hx hx'
              have : (m:ℝ)+1 ≤ (n:ℝ) := by norm_cast
              linarith only [hx.1.2, hx'.1.1, this]
            intro n _
            exact MeasureTheory.IntegrableOn.mono_set hinteg (Set.inter_subset_right _ I)
          _ ≤ _ := by
            apply MeasureTheory.set_integral_mono_set hinteg
            . apply Filter.eventually_of_mem (self_mem_ae_restrict hmes)
              intro x hx
              simp [hnonneg x (hI' hx)]
            apply HasSubset.Subset.eventuallyLE
            simp
      _ = _ := by simp
  have {x : ℝ} (hx: x ∈ Set.Icc a b) : ∫ t in Set.Ico x (x+1) ∩ I, f t ≤ f x := calc
    _ ≤ ∫ _ in Set.Ico x (x+1) ∩ I, f x := by
      apply MeasureTheory.set_integral_mono_on _ _ (MeasurableSet.inter measurableSet_Ico hmes) _
      . exact MeasureTheory.IntegrableOn.mono_set hinteg (Set.inter_subset_right _ I)
      . apply MeasureTheory.IntegrableOn.mono_set _ (Set.inter_subset_left _ _)
        simp
      intro y hy
      simp at hy
      exact hf hx (hI' hy.2) hy.1.1
    _ ≤ ∫ _ in Set.Ico x (x+1), f x := by
      apply MeasureTheory.set_integral_mono_set
      . simp
      . apply Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ico)
        intro y _
        simp [hnonneg x hx]
      exact HasSubset.Subset.eventuallyLE (Set.inter_subset_left _ I)
    _ = _ := by simp
  calc
    _ ≥ ∑ n in discretize I, ∫ t in (Set.Ico (n:ℝ) ((n:ℝ)+1) ∩ I), f t ∂ volume := by
      apply Finset.sum_le_sum
      intro n hn
      rw [discretize_mem hu hl n] at hn
      exact this (hI' hn)
    _ ≥ ∑ n in discretize I, ∫ t in (Set.Ico (n:ℝ) ((n:ℝ)+1) ∩ I), f t ∂ volume + ∫ t in (Set.Ico a (a+1) ∩ I), f t ∂ volume - f a := by
      simp
      exact this (Set.left_mem_Icc.mpr h)
    _ ≥ ∫ t in (⋃ n ∈ discretize I, (Set.Ico (n:ℝ) ((n:ℝ)+1) ∩ I)), f t ∂ volume  + ∫ t in (Set.Ico a (a+1) ∩ I), f t ∂ volume - f a := by
      simp
      apply integ_on_biunion_le_sum_integ hinteg
      . intro x hx
        exact hnonneg x (hI' hx)
      . intro i _
        exact MeasurableSet.inter measurableSet_Ico hmes
      intro i _
      exact Set.inter_subset_right _ I
    _ ≥ ∫ t in I, f t ∂ volume - f a := by
      simp
      convert integ_on_union_le_add_integ hinteg ?_ ?_ ?_ ?_ ?_
      . ext x; constructor
        . intro hx
          rcases le_iff_lt_or_eq.mp h with h' | h'
          swap
          . have := h'.symm ▸ (hI' hx)
            simp at this
            simp [this]
            right; exact this ▸ hx
          have hglb : IsGLB I a := by
            rw [isGLB_iff_le_iff]
            intro y
            constructor
            . intro hy
              apply lowerBounds_mono hI' hy
              rw [lowerBounds_Icc h]
              exact Set.right_mem_Iic
            intro hy
            replace hy := lowerBounds_mono hI (Eq.le rfl) hy
            rw [lowerBounds_Ioo h'] at hy
            exact hy
          have := unit_interval_cover hu hl hglb hx
          simp at this ⊢
          rcases this with ⟨ h1, h2 ⟩ | ⟨ i, hi, hi', hi'' ⟩
          . right; exact ⟨ ⟨ h1, h2 ⟩, hx⟩
          left; exact ⟨ i, ⟨ ⟨ hi, hi''⟩, hi', hx ⟩ ⟩
        simp
        intro this
        rcases this with ⟨ i, hi⟩ | h
        . exact hi.2.2
        exact h.2
      . intro x hx
        exact hnonneg x (hI' hx)
      . apply Finset.measurableSet_biUnion
        intro n _
        exact MeasurableSet.inter measurableSet_Ico hmes
      . exact MeasurableSet.inter measurableSet_Ico hmes
      . simp
      exact Set.inter_subset_right _ I
    _ = _ := by simp

lemma sum_approx_eq_integral_monotone {a b:ℝ} (h: a ≤ b) (f: ℝ → ℝ) (hf: MonotoneOn f (Set.Icc a b)) (hf': f a ≥ 0) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : ∑ n in discretize I, f n =[1] ∫ t in I, f t ∂ volume + O( f b ) := by
  have hu : BddAbove I := BddAbove.mono hI' bddAbove_Icc
  have hl : BddBelow I := BddBelow.mono hI' bddBelow_Icc
  have hI'_neg : { x | -x ∈ I } ⊆ Set.Icc (-b) (-a) := by
    intro x hx
    simp at hx ⊢
    replace hx := Set.mem_Icc.mp (hI' hx)
    exact ⟨ neg_le.mp hx.2, le_neg.mp hx.1 ⟩
  have hu' : BddAbove { x | -x ∈ I } := BddAbove.mono hI'_neg bddAbove_Icc
  have hl' : BddBelow { x | -x ∈ I } := BddBelow.mono hI'_neg bddBelow_Icc
  convert sum_approx_eq_integral_antitone (neg_le_neg h) (fun x ↦ f (-x)) ?_ ?_ { x | -x ∈ I } ?_ hI'_neg using 1
  . congr 1
    . convert Finset.sum_image ?_ (g := fun x ↦ -x)
      . ext n
        simp
        simp_rw [discretize_mem hu hl, discretize_mem hu' hl']
        simp
        constructor
        . intro hn; use -n
          simp [hn]
        intro this; rcases this with ⟨ a, ha, ha' ⟩
        simp [<-ha', ha]
      . rw [Int.cast_neg]
      intro x _ y _
      simp
    convert MeasurableEmbedding.set_integral_map (μ := volume) (Homeomorph.neg ℝ).closedEmbedding.measurableEmbedding f I using 1
    congr
    exact (Measure.map_neg_eq_self volume).symm
  . rw [neg_neg]
  . intro x hx y hy hxy
    simp at hx hy ⊢
    apply hf _ _ (neg_le_neg hxy)
    . exact Set.mem_Icc.mpr ⟨ le_neg.mp hy.2, neg_le.mp hy.1 ⟩
    exact Set.mem_Icc.mpr ⟨ le_neg.mp hx.2, neg_le.mp hx.1 ⟩
  . simp [hf']
  intro x hx
  simp at hx ⊢
  exact hI (Set.mem_Ioo.mpr ⟨ lt_neg.mp hx.2, neg_lt.mp hx.1 ⟩)


lemma sum_approx_eq_integral {a b c:ℝ} (h: a ≤ b) (f: ℝ → E)  (hderiv: ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (hcont': ContinuousOn (deriv f) (Set.Icc a b)) (hc: c ∈ Set.Icc a b) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : ∑ n in discretize I, f n =[1] ∫ t in I, f t ∂ volume + O( ‖f c‖ + ∫ t in I, ‖deriv f t‖ ∂ volume) := by
  have hu : BddAbove I := BddAbove.mono hI' bddAbove_Icc
  have hl : BddBelow I := BddBelow.mono hI' bddBelow_Icc
  have hmes: MeasurableSet I := by
    rw [<-measurableSet_insert (a := a), <-measurableSet_insert (a := b)]
    convert measurableSet_Icc (a := a) (b := b)
    ext x
    simp
    constructor
    . intro this
      rcases this with this | this | this
      . simp [this, h]
      . simp [this, h]
      exact Set.mem_Icc.mp (hI' this)
    intro this
    rcases le_iff_lt_or_eq.mp this.1 with h1 | h1
    . rcases le_iff_lt_or_eq.mp this.2 with h2 | h2
      . right; right; apply hI
        simp [h1, h2]
      simp [h2]
    simp [h1]
  let χ : ℝ → ℝ → ℤ := fun s ↦ fun x ↦ if s ≥ c then (if x ≥ s then 1 else 0) else -(if x ≤ s then 1 else 0)
  have repr : ∀ x ∈ Set.Icc a b, f x = f c + ∫ s in Set.Icc a b, (χ s x) • deriv f s ∂ volume := ftoc f hderiv hcont' hc
  have split_lhs : ∑ n in discretize I, f n = ∑ n in discretize I, f c + ∫ s in Set.Icc a b, ∑ n in discretize I, (χ s n) • deriv f s := by
    rw [integral_finset_sum, <-Finset.sum_add_distrib]
    . apply Finset.sum_congr rfl
      intro n hn
      exact repr n (hI' ((discretize_mem hu hl n).mp hn))
    intro n hn
    convert_to Integrable (μ := Measure.restrict volume (Set.Icc a b)) fun s ↦ (χ s n:ℝ) • (deriv f s)
    . ext s
      exact zsmul_eq_smul_cast ℝ (χ s ↑n) (deriv f s)
    rw [<-integrableOn_def]
    apply IntegrableOn.smul_continuousOn _ hcont' isCompact_Icc
    rcases le_or_gt c n with h | h
    . have : (fun x ↦ (χ x n:ℝ)) = Set.indicator (Set.Icc c n) 1 := by
        ext x
        simp [χ, Set.indicator]
        by_cases h' : c ≤ x
        . simp [h']
        simp [h']
        contrapose! h'
        exact h.trans h'
      rw [this]
      apply IntegrableOn.indicator _ measurableSet_Icc
      convert_to IntegrableOn (fun _ ↦ (1:ℝ)) (Set.Icc a b)
      rw [integrableOn_const]
      simp
    have : (fun x ↦ (χ x n:ℝ)) = Set.indicator (Set.Ico (n:ℝ) c) (-1) := by
      ext x
      simp [χ, Set.indicator]
      by_cases h' : x ≤ n
      . have : ¬ c ≤ x := by
          contrapose! h'
          exact lt_of_lt_of_le h h'
        simp [h', this, not_le.mp this]
        by_cases h'': n ≤ x
        all_goals simp [h'']
      simp [h']
      rcases le_or_gt c x with h'' | h''
      . simp [h'', not_lt.mpr h'']
      simp [h'',not_le.mpr h'']
      by_cases h'': n ≤ x
      all_goals simp [h'']
    rw [this]
    apply IntegrableOn.indicator _ measurableSet_Ico
    convert_to IntegrableOn (fun _ ↦ (-1:ℝ)) (Set.Icc a b)
    rw [integrableOn_const]
    simp
  have split_rhs : ∫ t in I, f t ∂ volume = ∫ t in I, f c ∂ volume + ∫ s in Set.Icc a b, (∫ t in I, (χ s t) • deriv f s ∂ volume) ∂ volume := by
    have : Integrable (fun x ↦ χ x.1 x.2 • deriv f x.1) (Measure.prod (Measure.restrict volume (Set.Icc a b)) (Measure.restrict volume I)) := by
      convert_to Integrable (μ := Measure.restrict volume ((Set.Icc a b) ×ˢ I)) fun x ↦ (χ x.1 x.2:ℝ) • (deriv f x.1)
      . ext x
        exact zsmul_eq_smul_cast ℝ (χ x.1 x.2) (deriv f x.1)
      . apply Measure.prod_restrict
      rw [<-integrableOn_def]
      apply MeasureTheory.IntegrableOn.mono_set (IntegrableOn.smul_continuousOn _ _ (IsCompact.prod isCompact_Icc isCompact_Icc)) (Set.prod_mono_right hI')
      . have : (fun x:ℝ × ℝ ↦ (χ x.1 x.2:ℝ)) = Set.indicator ({ x| c ≤ x.1} ∩ {x| x.1 ≤ x.2 }) 1 + Set.indicator ({x| x.2 ≤ x.1} ∩ {x|x.1 < c}) (-1) := by
          ext x
          simp [Set.indicator, χ]
          by_cases h: c ≤ x.1
          all_goals try simp [h]
          by_cases h': x.2 ≤ x.1
          all_goals try simp [h', not_le.mp h]
        rw [this]
        apply Integrable.add
        . rw [<-integrableOn_def]
          apply IntegrableOn.indicator
          . convert_to IntegrableOn (fun _ ↦ (1:ℝ)) (Set.Icc a b ×ˢ (Set.Icc a b))
            rw [integrableOn_const, Measure.volume_eq_prod, Measure.prod_prod]
            simp [<-ENNReal.ofReal_mul (sub_nonneg.mpr h)]
          exact MeasurableSet.inter (measurableSet_le measurable_const measurable_fst) (measurableSet_le measurable_fst measurable_snd)
        rw [<-integrableOn_def]
        apply IntegrableOn.indicator
        . convert_to IntegrableOn (fun _ ↦ (-1:ℝ)) (Set.Icc a b ×ˢ (Set.Icc a b))
          rw [integrableOn_const, Measure.volume_eq_prod, Measure.prod_prod]
          simp [<-ENNReal.ofReal_mul (sub_nonneg.mpr h)]
        exact MeasurableSet.inter (measurableSet_le measurable_snd measurable_fst) (measurableSet_lt measurable_fst measurable_const)
      apply ContinuousOn.comp (g := deriv f) (f := Prod.fst) (t := Set.Icc a b) hcont' (Continuous.continuousOn continuous_fst)
      intro x hx
      exact (Set.mem_prod.mp hx).1
    rw [integral_integral_swap, <-integral_add]
    . apply set_integral_congr hmes
      intro x hx
      exact repr x (hI' hx)
    . rw [<-integrableOn_def, integrableOn_const]
      right
      exact lt_of_le_of_lt (measure_mono hI')  measure_Icc_lt_top
    . convert Integrable.integral_prod_right (f := fun x ↦ χ x.1 x.2 • deriv f x.1) this
    exact this
  rw [split_lhs, split_rhs]
  apply add_of_eqPlusBigO _ _
  . sorry
  sorry


lemma sum_approx_eq_integral_antitone_nat_ico {a b:ℝ} (h0: 0 ≤ a) (h: a ≤ b) (f: ℝ → ℝ) (hf: AntitoneOn f (Set.Icc a b)) (hf': f b ≥ 0) : ∑ n in Finset.Ico ⌈ a ⌉₊ ⌈ b ⌉₊, f n =[1] ∫ t in Set.Ico a b, f t ∂ volume + O( f a ) := by
  convert sum_approx_eq_integral_antitone h f hf hf' (Set.Ico a b) Set.Ioo_subset_Ico_self Set.Ico_subset_Icc_self
  change ∑ n in Finset.Ico ⌈ a ⌉₊ ⌈ b ⌉₊, f (n:ℤ) = ∑ n in discretize (Set.Ico a b), f ↑n
  rw [<-Finset.sum_image (g := fun n:ℕ ↦ (n:ℤ)) (f := fun n:ℤ ↦ f n)]
  congr
  rw [<-Finset.coe_inj,discretize_Ico_nonneg h0 (h0.trans h), Finset.coe_image, Finset.coe_Ico]
  simp

lemma sum_approx_eq_integral_monotone_nat_ico {a b:ℝ} (h0: 0 ≤ a) (h: a ≤ b) (f: ℝ → ℝ) (hf: MonotoneOn f (Set.Icc a b)) (hf': f a ≥ 0) : ∑ n in Finset.Ico ⌈ a ⌉₊ ⌈ b ⌉₊, f n =[1] ∫ t in Set.Ico a b, f t ∂ volume + O( f b ) := by
  convert sum_approx_eq_integral_monotone h f hf hf' (Set.Ico a b) Set.Ioo_subset_Ico_self Set.Ico_subset_Icc_self
  change ∑ n in Finset.Ico ⌈ a ⌉₊ ⌈ b ⌉₊, f (n:ℤ) = ∑ n in discretize (Set.Ico a b), f ↑n
  rw [<-Finset.sum_image (g := fun n:ℕ ↦ (n:ℤ)) (f := fun n:ℤ ↦ f n)]
  congr
  rw [<-Finset.coe_inj,discretize_Ico_nonneg h0 (h0.trans h), Finset.coe_image, Finset.coe_Ico]
  simp

lemma sum_approx_eq_integral_antitone_nat_icc {a b:ℝ} (h0: 0 ≤ a) (h: a ≤ b) (f: ℝ → ℝ) (hf: AntitoneOn f (Set.Icc a b)) (hf': f b ≥ 0) : ∑ n in Finset.Icc ⌈ a ⌉₊ ⌊ b ⌋₊, f n =[1] ∫ t in Set.Icc a b, f t ∂ volume + O( f a ) := by
  convert sum_approx_eq_integral_antitone h f hf hf' (Set.Icc a b) Set.Ioo_subset_Icc_self (Eq.subset rfl)
  change ∑ n in Finset.Icc ⌈ a ⌉₊ ⌊ b ⌋₊, f (n:ℤ) = ∑ n in discretize (Set.Icc a b), f ↑n
  rw [<-Finset.sum_image (g := fun n:ℕ ↦ (n:ℤ)) (f := fun n:ℤ ↦ f n)]
  congr
  rw [<-Finset.coe_inj,discretize_Icc_nonneg h0 (h0.trans h), Finset.coe_image, Finset.coe_Icc]
  simp

lemma sum_approx_eq_integral_monotone_nat_icc {a b:ℝ} (h0: 0 ≤ a) (h: a ≤ b) (f: ℝ → ℝ) (hf: MonotoneOn f (Set.Icc a b)) (hf': f a ≥ 0) : ∑ n in Finset.Icc ⌈ a ⌉₊ ⌊ b ⌋₊, f n =[1] ∫ t in Set.Icc a b, f t ∂ volume + O( f b ) := by
  convert sum_approx_eq_integral_monotone h f hf hf' (Set.Icc a b) Set.Ioo_subset_Icc_self (Eq.subset rfl)
  change ∑ n in Finset.Icc ⌈ a ⌉₊ ⌊ b ⌋₊, f (n:ℤ) = ∑ n in discretize (Set.Icc a b), f ↑n
  rw [<-Finset.sum_image (g := fun n:ℕ ↦ (n:ℤ)) (f := fun n:ℤ ↦ f n)]
  congr
  rw [<-Finset.coe_inj,discretize_Icc_nonneg h0 (h0.trans h), Finset.coe_image, Finset.coe_Icc]
  simp
