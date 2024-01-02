import Asymptotic.majorize
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Set.Card

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

lemma sub_eq (a b: ℕ) : (a-b:ℕ) = max 0 (a-b:ℝ) := by
    rcases le_or_lt b a with h | h
    . zify [h]
      apply (max_eq_right (sub_nonneg.mpr _)).symm
      norm_cast
    simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]
    apply (max_eq_left (sub_nonpos.mpr _)).symm
    norm_cast
    exact Nat.le_of_lt h

lemma int_to_nat_eq (a:ℤ) : Int.toNat a = max (0:ℝ) a := by
  norm_cast
  rcases le_or_lt 0 a with h | h
  . rcases Int.eq_ofNat_of_zero_le h with ⟨n, rfl⟩
    simp
  simp [Int.toNat_eq_zero.mpr (le_of_lt h), (le_of_lt h)]

lemma interval_count {a b: ℝ} (h: a ≤ b) (I: Set ℝ) (hI: Set.Ioo a b ⊆ I) (hI': I ⊆ Set.Icc a b) : Nat.card (I ∩ (Set.range fun (n:ℤ) ↦ (n:ℝ)) : Set ℝ) =[1] b-a + O(1) := by
  set ι := fun (n:ℤ) ↦ (n:ℝ)
  set Z := Set.range ι
  rw [Asymptotics.eqPlusBigO_iff_le_and_ge, mul_one]
  have hi : I ∩ Z ⊆ ι '' (Set.Ioo (⌈a⌉-1) (⌊b⌋+1)) := by
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
  have hfin : Set.Finite (I ∩ Z) := Set.Finite.subset hfin' hi
  constructor
  . apply (Nat.cast_le.mpr (Nat.card_mono hfin' hi)).trans
    rw [Nat.card_image_of_injective Int.cast_injective _]
    simp
    rw [sub_eq, max_le_iff]
    constructor
    . linarith only [h]
    rw [sub_le_iff_le_add, int_to_nat_eq, max_le_iff]
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
  replace this : ι '' Set.Icc (⌊a⌋ + 1) (⌈b⌉ - 1) ⊆ I ∩ Z := Set.subset_inter this (Set.image_subset_range _ _)
  apply LE.le.trans _ (Nat.cast_le.mpr (Nat.card_mono hfin this))
  rw [Nat.card_image_of_injective Int.cast_injective _]
  simp [int_to_nat_eq]
  right
  linarith only [Int.floor_le a, Int.le_ceil b]





-- show that  sum_{n in I cap Z} f =[1] int_I f + O(|| f ||_TV); approximate the TV function uniformly by a step function and use previous lemma.  Valid in normed spaces!
