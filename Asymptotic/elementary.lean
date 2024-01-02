import Asymptotic.majorize
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Calculus.Deriv.Basic

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

lemma ftoc {a b c:ℝ} (h: a ≤ b) (f: ℝ → E) (hcont: ContinuousOn f (Set.Icc a b))  (hderiv: DifferentiableOn ℝ f (Set.Ioo a b)) (hcont': ContinuousOn (deriv f) (Set.Icc a b))
 (hc: c ∈ Set.Icc a b) : ∀ x ∈ Set.Icc a b, f x = f c + ∫ t in Set.Ioo a b, (if x ≥ c then (if x ≥ t then 1 else 0) else -(if x ≤ t then 1 else 0)) • deriv f t ∂ volume := by
  sorry

open Classical

noncomputable def discretize (I: Set ℝ) : Finset ℤ := if h : Set.Finite {n:ℤ | (n:ℝ) ∈ I } then h.toFinset else ∅


lemma sum_approx_eq_integral {a b c:ℝ} (h: a ≤ b) (f: ℝ → E) (hcont: ContinuousOn f (Set.Icc a b))  (hderiv: DifferentiableOn ℝ f (Set.Ioo a b)) (hcont': ContinuousOn (deriv f) (Set.Icc a b)) (hc: c ∈ Set.Icc a b) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : ∑ n in discretize I, f n =[1] ∫ t in I, f t ∂ volume + O( ‖f c‖ + ∫ t in I, ‖deriv f t‖ ∂ volume) := by
  simp
  sorry
