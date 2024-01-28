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

lemma interval_mes {a b: ℝ} (h: a ≤ b) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : ENNReal.toReal (MeasureTheory.volume I) = b-a := by
    convert ENNReal.toReal_ofReal (sub_nonneg.mpr h)
    apply le_antisymm
    . convert MeasureTheory.measure_mono hI'
      simp
    convert MeasureTheory.measure_mono hI
    simp

lemma interval_count' {I: Set ℝ} (hI: Set.OrdConnected I) (hbound: OrdBounded I) : Finset.card I.discretize =[1] ENNReal.toReal (MeasureTheory.volume I) + O(1) := by
  rcases interval_iff_ord_connected_ordbounded.mp ⟨ hI, hbound ⟩ with ⟨ a, b, h, hI, hI' ⟩
  convert interval_count h I hI hI'
  exact interval_mes h I hI hI'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

open BigOperators MeasureTheory

noncomputable def cutoff (c x t :ℝ) : ℝ := (if  t ≤ x then 1 else 0) - (if t ≤ c then 1 else 0)

lemma cutoff_eq (c x:ℝ) : cutoff c x = if c ≤  x then Set.indicator (Set.Ioc c x) 1 else Set.indicator (Set.Ioc x c) (-1) := by
  ext t
  by_cases h : t ≤ x
  . by_cases h' : t ≤ c
    . by_cases h'' : c ≤ x
      . simp [h, h', h'', not_lt.mpr h', Set.indicator, cutoff]
      simp [h, h', h'', not_lt.mpr h, Set.indicator, cutoff]
    simp [h, h', not_le.mp h', (le_of_lt (not_le.mp h')).trans h, Set.indicator, cutoff]
  by_cases h' : t ≤ c
  . simp [h, h', not_le.mp h, not_le.mpr (lt_of_lt_of_le (not_le.mp h) h'), Set.indicator, cutoff]
  by_cases h'' : c ≤ x
  all_goals simp [h,h', h'',Set.indicator, cutoff]

lemma ftoc {a b c:ℝ} (f: ℝ → E) (hderiv: ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (hcont': ContinuousOn (deriv f) (Set.Icc a b))
 (hc: c ∈ Set.Icc a b) : ∀ x ∈ Set.Icc a b, f x = f c + ∫ t in Set.Icc a b, (cutoff c x t) • deriv f t ∂ volume := by
  intro x hx
  simp at hc
  by_cases h : c ≤ x
  . have (t:ℝ) :  (Set.indicator (Set.Ioc c x) (1:ℝ → ℝ) t) • (deriv f t) =  Set.indicator (Set.Ioc c x) (deriv f) t := by
      rw [<-Set.indicator_smul_apply_left]
      simp
    simp [cutoff_eq, h, this]
    have inc : Set.Icc a b ∩ Set.Ioc c x = Set.Ioc c x := by
      simp
      intro t ht
      simp at hx ht ⊢
      exact ⟨ hc.1.trans (le_of_lt ht.1), ht.2.trans hx.2 ⟩
    have inc' : Set.uIcc c x ⊆ Set.Icc a b := by
      intro t ht
      simp [h] at hx ht ⊢
      exact ⟨ hc.1.trans ht.1, ht.2.trans hx.2 ⟩
    rw [set_integral_indicator measurableSet_Ioc, inc, <- intervalIntegral.integral_of_le h, intervalIntegral.integral_deriv_eq_sub' f (by rfl) _ (ContinuousOn.mono hcont' inc')]
    . exact eq_add_of_sub_eq' rfl
    intro t ht
    exact hderiv t (inc' ht)
  have (t:ℝ) :  (Set.indicator (Set.Ioc x c) (-(1:ℝ → ℝ)) t) • (deriv f t) =  -Set.indicator (Set.Ioc x c) (deriv f) t := by
      rw [<-Set.indicator_smul_apply_left]
      simp [Set.indicator_neg]
  simp [cutoff_eq, h, this]
  have inc : Set.Icc a b ∩ Set.Ioc x c = Set.Ioc x c := by
      simp
      intro t ht
      simp at hx ht ⊢
      exact ⟨ hx.1.trans (le_of_lt ht.1), ht.2.trans hc.2 ⟩
  have inc' : Set.uIcc x c ⊆ Set.Icc a b := by
      intro t ht
      simp [le_of_lt (not_le.mp h)] at hx ht ⊢
      exact ⟨ hx.1.trans ht.1, ht.2.trans hc.2 ⟩
  rw [integral_neg, set_integral_indicator measurableSet_Ioc, inc,  <- intervalIntegral.integral_of_le (le_of_lt (not_le.mp h)), intervalIntegral.integral_deriv_eq_sub' f (by rfl) _ (ContinuousOn.mono hcont' inc')]
  . abel
  intro t ht
  exact hderiv t (inc' ht)


open Asymptotics


lemma unit_interval_subset_or_inf {I : Set ℝ} [hI: Set.OrdConnected I]  (hbound: OrdBounded I) {n : ℤ} (hn: n ∈ I.discretize) (hsub: ¬ IsLeast I.discretize n) : Set.Ico ((n:ℝ)-1) (n:ℝ) ⊆ I := by
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
    . exact (Set.discretize_mem hbound m).mp hm
    exact (Set.discretize_mem hbound n).mp hn
  apply sub
  have : (m:ℝ) ≤ (n:ℝ)-1 := by norm_cast; linarith only [hx2]
  simp; refine ⟨ this.trans ?_, le_of_lt hx1.2 ⟩; linarith only [hx1.1]

lemma unit_interval_cover {I : Set ℝ} [hI: Set.OrdConnected I]  (hbound: OrdBounded I) {a : ℝ} (ha: IsGLB I a) : I ⊆ (Set.Ico a (a+1)) ∪ ⋃ n ∈ I.discretize, Set.Ico (n:ℝ) (n+1) := by
  intro x hx
  simp
  rw [or_iff_not_imp_left]
  intro ha'
  replace ha' : x ≥ a+1 := by
    contrapose! ha'
    exact ⟨ (Set.mem_of_mem_inter_left ha) hx, ha' ⟩
  use ⌊ x ⌋
  refine ⟨ Int.floor_le x, ?_, Int.lt_floor_add_one x ⟩
  rw [Set.discretize_mem hbound _]
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
    classical
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


lemma sum_approx_eq_integral_antitone {a b:ℝ} (h: a ≤ b) (f: ℝ → ℝ) (hf: AntitoneOn f (Set.Icc a b)) (hf': f b ≥ 0) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : ∑ n in I.discretize, f n =[1] ∫ t in I, f t ∂ volume + O( f a ) := by
  rcases interval_iff_ord_connected_ordbounded.mpr ⟨ a, b, h, hI, hI' ⟩ with ⟨ hc, hbound ⟩
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

  classical
  rw [eqPlusBigO_iff_le_and_ge]
  constructor
  . calc
      _ ≤ ∑ n in I.discretize, ((∫ t in (Set.Ico ((n:ℝ)-1) (n:ℝ)) ∩ I, f t ∂ volume) + if (IsLeast I.discretize n) then (f a) else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hmin : IsLeast I.discretize n
        . simp [hmin]
          rw [Set.discretize_mem hbound] at hn
          apply (hf (Set.left_mem_Icc.mpr h) (hI' hn) ((Set.mem_Icc.mp (hI' hn)).1)).trans
          rw [le_add_iff_nonneg_left]
          apply MeasureTheory.set_integral_nonneg (MeasurableSet.inter measurableSet_Ico hmes)
          intro x hx
          simp at hx
          exact hnonneg x (hI' hx.2)
        simp [hmin]
        replace hmin := unit_interval_subset_or_inf hbound hn hmin
        rw [Set.inter_eq_left.mpr hmin]
        calc
          _ = ∫ _ in Set.Ico ((n:ℝ)-1) (n:ℝ), f n ∂ volume := by
            simp
          _ ≤ _ := by
            apply MeasureTheory.set_integral_mono_on _ _ measurableSet_Ico _
            . simp
            . exact MeasureTheory.IntegrableOn.mono_set hinteg hmin
            intro x hx
            exact hf (hI' (hmin hx)) (hI' ((Set.discretize_mem hbound n).mp hn)) (le_of_lt hx.2)
      _ ≤ ∑ n in I.discretize, (∫ t in (Set.Ico ((n:ℝ)-1) (n:ℝ)) ∩ I, f t ∂ volume) + f a := by
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
          _ = ∫ t in ⋃ n ∈ I.discretize, (Set.Ico ((n:ℝ)-1) (n:ℝ) ∩ I), f t ∂ volume := by
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
    _ ≥ ∑ n in I.discretize, ∫ t in (Set.Ico (n:ℝ) ((n:ℝ)+1) ∩ I), f t ∂ volume := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Set.discretize_mem hbound n] at hn
      exact this (hI' hn)
    _ ≥ ∑ n in I.discretize, ∫ t in (Set.Ico (n:ℝ) ((n:ℝ)+1) ∩ I), f t ∂ volume + ∫ t in (Set.Ico a (a+1) ∩ I), f t ∂ volume - f a := by
      simp
      exact this (Set.left_mem_Icc.mpr h)
    _ ≥ ∫ t in (⋃ n ∈ I.discretize, (Set.Ico (n:ℝ) ((n:ℝ)+1) ∩ I)), f t ∂ volume  + ∫ t in (Set.Ico a (a+1) ∩ I), f t ∂ volume - f a := by
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
          have := unit_interval_cover hbound hglb hx
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

lemma sum_approx_eq_integral_monotone {a b:ℝ} (h: a ≤ b) (f: ℝ → ℝ) (hf: MonotoneOn f (Set.Icc a b)) (hf': f a ≥ 0) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : ∑ n in I.discretize, f n =[1] ∫ t in I, f t ∂ volume + O( f b ) := by
  rcases interval_iff_ord_connected_ordbounded.mpr ⟨ a, b, h, hI, hI' ⟩ with ⟨ _, hbound ⟩
  have hI'_neg : { x | -x ∈ I } ⊆ Set.Icc (-b) (-a) := by
    intro x hx
    simp at hx ⊢
    replace hx := Set.mem_Icc.mp (hI' hx)
    exact ⟨ neg_le.mp hx.2, le_neg.mp hx.1 ⟩
  have hbound' : OrdBounded { x | -x ∈ I } := OrdBounded.mono hI'_neg (OrdBounded.icc (-b) (-a))
  convert sum_approx_eq_integral_antitone (neg_le_neg h) (fun x ↦ f (-x)) ?_ ?_ { x | -x ∈ I } ?_ hI'_neg using 1
  . congr 1
    . convert Finset.sum_image ?_ (g := fun x ↦ -x)
      . ext n
        simp
        simp_rw [Set.discretize_mem hbound, Set.discretize_mem hbound']
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


lemma sum_approx_eq_integral {a b c:ℝ} (h: a ≤ b) (f: ℝ → E)  (hderiv: ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (hcont': ContinuousOn (deriv f) (Set.Icc a b)) (hc: c ∈ Set.Icc a b) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : ∑ n in I.discretize, f n =[1] ∫ t in I, f t ∂ volume + O( ‖f c‖ + ∫ t in Set.Icc a b, ‖deriv f t‖ ∂ volume) := by
  rcases interval_iff_ord_connected_ordbounded.mpr ⟨ a, b, h, hI, hI' ⟩ with ⟨ _, hbound ⟩
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
  have repr := ftoc f hderiv hcont' hc
  have split_lhs : ∑ n in I.discretize, f n = ∑ n in I.discretize, f c + ∫ s in Set.Icc a b, ∑ n in I.discretize, (cutoff c n s) • deriv f s := by
    rw [integral_finset_sum, <-Finset.sum_add_distrib]
    . apply Finset.sum_congr rfl
      intro n hn
      exact repr n (hI' ((Set.discretize_mem hbound n).mp hn))
    intro n hn
    rw [<-integrableOn_def]
    apply IntegrableOn.smul_continuousOn _ hcont' isCompact_Icc
    rcases le_or_gt c n with h | h
    . simp [cutoff_eq, h]
      apply IntegrableOn.indicator _ measurableSet_Ioc
      convert_to IntegrableOn (fun _ ↦ (1:ℝ)) (Set.Icc a b)
      rw [integrableOn_const]
      simp
    simp [cutoff_eq, not_le.mpr h]
    apply IntegrableOn.indicator _ measurableSet_Ioc
    convert_to IntegrableOn (fun _ ↦ (-1:ℝ)) (Set.Icc a b)
    rw [integrableOn_const]
    simp
  have split_rhs : ∫ t in I, f t ∂ volume = ∫ t in I, f c ∂ volume + ∫ s in Set.Icc a b, (∫ t in I, (cutoff c t s) • deriv f s ∂ volume) ∂ volume := by
    have : Integrable (fun x ↦ cutoff c x.2 x.1 • deriv f x.1) (Measure.prod (Measure.restrict volume (Set.Icc a b)) (Measure.restrict volume I)) := by
      rw [Measure.prod_restrict,<-integrableOn_def]
      apply MeasureTheory.IntegrableOn.mono_set (IntegrableOn.smul_continuousOn _ _ (IsCompact.prod isCompact_Icc isCompact_Icc)) (Set.prod_mono_right hI')
      . simp_rw [cutoff]
        apply Integrable.add
        . rw [<-integrableOn_def]
          apply IntegrableOn.indicator
          . convert_to IntegrableOn (fun _ ↦ (1:ℝ)) (Set.Icc a b ×ˢ (Set.Icc a b))
            rw [integrableOn_const, Measure.volume_eq_prod, Measure.prod_prod]
            simp [<-ENNReal.ofReal_mul (sub_nonneg.mpr h)]
          exact measurableSet_le measurable_fst measurable_snd
        have : (fun (x: ℝ × ℝ) ↦ -if x.1 ≤ c then (1:ℝ) else 0) = (fun (x: ℝ × ℝ) ↦ if x.1 ≤ c then (-1:ℝ) else 0) := by
          ext x
          by_cases h : x.1 ≤ c
          all_goals simp [h]
        rw [<-integrableOn_def, this]
        apply IntegrableOn.indicator
        . convert_to IntegrableOn (fun _ ↦ (-1:ℝ)) (Set.Icc a b ×ˢ (Set.Icc a b))
          rw [integrableOn_const, Measure.volume_eq_prod, Measure.prod_prod]
          simp [<-ENNReal.ofReal_mul (sub_nonneg.mpr h)]
        exact measurableSet_le measurable_fst measurable_const
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
    . convert Integrable.integral_prod_right (f := fun x ↦ cutoff c x.2 x.1 • deriv f x.1) this
    exact this
  rw [split_lhs, split_rhs]
  apply add_of_eqPlusBigO _ _
  . simp [interval_mes h I hI hI']
    rw [nsmul_eq_smul_cast (R := ℝ), <-sub_smul, norm_smul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    have := interval_count h I hI hI'
    simp at this
    convert this using 1
  convert int_of_eqPlusBigO ?_ ?_ ?_ ?_ ?_
  . apply Filter.eventually_of_forall
    intro s hs
    simp
    rw [<-Finset.sum_smul, integral_smul_const, <-sub_smul, norm_smul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    by_cases h: s ≤ c
    . have (x:ℝ) : cutoff c x s = - Set.indicator (Set.Iio s) 1 x := by
        simp [cutoff, h, Set.indicator]
        by_cases h': s ≤ x
        . simp [h', not_lt.mpr h']
        simp [h', not_le.mp h']
      simp [this]
      sorry
    have (x:ℝ) : cutoff c x s = Set.indicator (Set.Ici s) 1 x := by
      simp [cutoff, h, Set.indicator]
    simp [this]
    rw [Finset.sum_indicator_eq_sum_filter]
    simp
    sorry
  . sorry
  . sorry
  sorry


lemma sum_approx_eq_integral_antitone_nat_ico {a b:ℝ} (h0: 0 ≤ a) (h: a ≤ b) (f: ℝ → ℝ) (hf: AntitoneOn f (Set.Icc a b)) (hf': f b ≥ 0) : ∑ n in Finset.Ico ⌈ a ⌉₊ ⌈ b ⌉₊, f n =[1] ∫ t in Set.Ico a b, f t ∂ volume + O( f a ) := by
  convert sum_approx_eq_integral_antitone h f hf hf' (Set.Ico a b) Set.Ioo_subset_Ico_self Set.Ico_subset_Icc_self
  change ∑ n in Finset.Ico ⌈ a ⌉₊ ⌈ b ⌉₊, f (n:ℤ) = ∑ n in (Set.Ico a b).discretize, f ↑n
  rw [<-Finset.sum_image (g := fun n:ℕ ↦ (n:ℤ)) (f := fun n:ℤ ↦ f n)]
  simp [Nat.cast_ceil_eq_int_ceil h0, Nat.cast_ceil_eq_int_ceil (h0.trans h)]
  intro x _ y _
  simp

lemma sum_approx_eq_integral_monotone_nat_ico {a b:ℝ} (h0: 0 ≤ a) (h: a ≤ b) (f: ℝ → ℝ) (hf: MonotoneOn f (Set.Icc a b)) (hf': f a ≥ 0) : ∑ n in Finset.Ico ⌈ a ⌉₊ ⌈ b ⌉₊, f n =[1] ∫ t in Set.Ico a b, f t ∂ volume + O( f b ) := by
  convert sum_approx_eq_integral_monotone h f hf hf' (Set.Ico a b) Set.Ioo_subset_Ico_self Set.Ico_subset_Icc_self
  change ∑ n in Finset.Ico ⌈ a ⌉₊ ⌈ b ⌉₊, f (n:ℤ) = ∑ n in (Set.Ico a b).discretize, f ↑n
  rw [<-Finset.sum_image (g := fun n:ℕ ↦ (n:ℤ)) (f := fun n:ℤ ↦ f n)]
  simp [Nat.cast_ceil_eq_int_ceil h0, Nat.cast_ceil_eq_int_ceil (h0.trans h)]
  intro x _ y _
  simp

lemma sum_approx_eq_integral_antitone_nat_icc {a b:ℝ} (h0: 0 ≤ a) (h: a ≤ b) (f: ℝ → ℝ) (hf: AntitoneOn f (Set.Icc a b)) (hf': f b ≥ 0) : ∑ n in Finset.Icc ⌈ a ⌉₊ ⌊ b ⌋₊, f n =[1] ∫ t in Set.Icc a b, f t ∂ volume + O( f a ) := by
  convert sum_approx_eq_integral_antitone h f hf hf' (Set.Icc a b) Set.Ioo_subset_Icc_self (Eq.subset rfl)
  change ∑ n in Finset.Icc ⌈ a ⌉₊ ⌊ b ⌋₊, f (n:ℤ) = ∑ n in (Set.Icc a b).discretize, f ↑n
  rw [<-Finset.sum_image (g := fun n:ℕ ↦ (n:ℤ)) (f := fun n:ℤ ↦ f n)]
  simp [Nat.cast_ceil_eq_int_ceil h0, Nat.cast_floor_eq_int_floor (h0.trans h)]
  intro x _ y _
  simp

lemma sum_approx_eq_integral_monotone_nat_icc {a b:ℝ} (h0: 0 ≤ a) (h: a ≤ b) (f: ℝ → ℝ) (hf: MonotoneOn f (Set.Icc a b)) (hf': f a ≥ 0) : ∑ n in Finset.Icc ⌈ a ⌉₊ ⌊ b ⌋₊, f n =[1] ∫ t in Set.Icc a b, f t ∂ volume + O( f b ) := by
  convert sum_approx_eq_integral_monotone h f hf hf' (Set.Icc a b) Set.Ioo_subset_Icc_self (Eq.subset rfl)
  change ∑ n in Finset.Icc ⌈ a ⌉₊ ⌊ b ⌋₊, f (n:ℤ) = ∑ n in (Set.Icc a b).discretize, f ↑n
  rw [<-Finset.sum_image (g := fun n:ℕ ↦ (n:ℤ)) (f := fun n:ℤ ↦ f n)]
  simp [Nat.cast_ceil_eq_int_ceil h0, Nat.cast_floor_eq_int_floor (h0.trans h)]
  intro x _ y _
  simp
