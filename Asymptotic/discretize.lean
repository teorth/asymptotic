import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Intervals.OrdConnected
import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.Data.Int.Interval
import Mathlib.Order.LocallyFinite
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Instances.Real

section ordBounded

variable {α : Type*} [Preorder α]

def OrdBounded (s : Set α) := (BddBelow s) ∧ (BddAbove s)

lemma OrdBounded.mono ⦃s : Set α⦄ ⦃t : Set α⦄ (h : s ⊆ t) :
OrdBounded t → OrdBounded s := by
  intro hb
  exact ⟨ BddBelow.mono h hb.1, BddAbove.mono h hb.2 ⟩

@[simp]
lemma OrdBounded.icc (a b:α) : OrdBounded (Set.Icc a b) := ⟨ bddBelow_Icc, bddAbove_Icc ⟩

@[simp]
lemma OrdBounded.ico (a b:α) : OrdBounded (Set.Ico a b) := ⟨ bddBelow_Ico, bddAbove_Ico ⟩

@[simp]
lemma OrdBounded.ioc (a b:α) : OrdBounded (Set.Ioc a b) := ⟨ bddBelow_Ioc, bddAbove_Ioc ⟩

@[simp]
lemma OrdBounded.ioo (a b:α) : OrdBounded (Set.Ioo a b) := ⟨ bddBelow_Ioo, bddAbove_Ioo ⟩

lemma ordBounded_of_subset_of_icc {α : Type*} [Preorder α] {s : Set α} {a b:α} (h: s ⊆ Set.Icc a b) : OrdBounded s := OrdBounded.mono h (OrdBounded.icc a b)

lemma ordBounded_def {α : Type*} [Preorder α] {s : Set α} : OrdBounded s ↔ (∃ a b, s ⊆ Set.Icc a b) := by
  constructor
  . intro h
    rcases bddBelow_def.mp h.1 with ⟨ a, ha ⟩
    rcases bddAbove_def.mp h.2 with ⟨ b, hb ⟩
    use a, b
    intro y hy
    simp [ha y hy, hb y hy]
  rintro ⟨ a, b, h ⟩
  exact ordBounded_of_subset_of_icc h

lemma ordBounded_iff_bounded {s: Set ℝ} : OrdBounded s ↔  Bornology.IsBounded s := Real.isBounded_iff_bddBelow_bddAbove.symm



end ordBounded

section toFinset'

noncomputable def Set.toFinset' {α: Type*} (s: Set α) : Finset α :=
  dite (h := Classical.dec (Set.Finite s)) Set.Finite.toFinset (fun _ ↦ ∅)

lemma Set.toFinset'_of_set_finite {α: Type*} {s: Set α} (h:Set.Finite s) : s.toFinset' = h.toFinset := by
  simp [h, Set.toFinset']

lemma Set.toFinset'_of_finite {α: Type*} {s: Set α} [Finite s] : s.toFinset' = s.toFinite.toFinset := by
  simp [toFinite s, Set.toFinset']

lemma Set.toFinset'_of_set_infinite {α: Type*} {s: Set α} (h: Set.Infinite s) : s.toFinset' = ∅ := by
  simp [mt Set.Finite.not_infinite (not_not_intro h), Set.toFinset']

lemma Set.toFinset'_of_infinite {α: Type*} {s: Set α} [h: Infinite s] : s.toFinset' = ∅ := by
  simp [mt Set.Finite.not_infinite (not_not_intro (infinite_coe_iff.mp h)), Set.toFinset']

@[simp]
lemma Set.toFinset'_of_fintype {α: Type*} (s: Set α) [Fintype s] : s.toFinset' = s.toFinset := by
  simp [Set.toFinite s, Set.toFinset']

lemma Set.mem_toFinset'_of_set_finite {α: Type*} {s: Set α} (h:Set.Finite s) (x:α) : x ∈ s.toFinset' ↔ x ∈ s := by
  simp [h, Set.toFinset']

lemma Set.mem_toFinset'_of_fintype {α: Type*} {s: Set α} [Fintype s] (x:α) : x ∈ s.toFinset' ↔ x ∈ s := by
  simp

end toFinset'

section set_of_int

lemma Int.finite_of_bounded {I: Set ℤ} (hbound: OrdBounded I) : Set.Finite I := by
  rcases ordBounded_def.mp hbound with ⟨ a, b, h ⟩
  apply Set.Finite.subset (Set.finite_Icc a b) h

lemma Int.Icc_toFinset' {a b:ℤ}: (Set.Icc a b).toFinset' = Finset.Icc a b := by simp

lemma Int.Ioc_toFinset' {a b:ℤ}: (Set.Ioc a b).toFinset' = Finset.Ioc a b := by simp

lemma Int.Ico_toFinset' {a b:ℤ}: (Set.Ico a b).toFinset' = Finset.Ico a b := by simp

lemma Int.Ioo_toFinset' {a b:ℤ}: (Set.Ioo a b).toFinset' = Finset.Ioo a b := by simp

end set_of_int

section set_of_real

lemma Real.bounded_of_discretized_of_bounded {I: Set ℝ} (hbound: OrdBounded I) : OrdBounded (((↑): ℤ → ℝ)⁻¹' I) := by
  rcases ordBounded_def.mp hbound with ⟨ a, b, h ⟩
  apply OrdBounded.mono (t := (((↑): ℤ → ℝ)⁻¹' (Set.Icc a b))) (Set.preimage_mono h)
  simp

lemma Real.finite_of_discretized_of_bounded {I: Set ℝ} (hbound: OrdBounded I) : Set.Finite (((↑): ℤ → ℝ)⁻¹' I) := Int.finite_of_bounded (bounded_of_discretized_of_bounded hbound)

end set_of_real

section nat_to_int

/-- The lemmas in this section are superseded in sufficiently recent versions of Mathlib -/
@[simp]
lemma Nat.image_cast_int_Ico (a b:ℕ) : (↑) '' (Set.Ico a b) = Set.Ico (a:ℤ) (b:ℤ) := by
  ext x
  simp
  constructor
  . rintro ⟨ n, ⟨ ha, hb⟩, rfl ⟩
    norm_cast
  rintro ⟨ ha, hb ⟩
  rcases Int.eq_ofNat_of_zero_le ((Int.zero_le_ofNat a).trans ha) with ⟨ n, rfl ⟩
  norm_cast at ha hb
  use n

@[simp]
lemma Nat.image_cast_int_Icc (a b:ℕ) : (↑) '' (Set.Icc a b) = Set.Icc (a:ℤ) (b:ℤ) := by
  ext x
  simp
  constructor
  . rintro ⟨ n, ⟨ ha, hb⟩, rfl ⟩
    norm_cast
  rintro ⟨ ha, hb ⟩
  rcases Int.eq_ofNat_of_zero_le ((Int.zero_le_ofNat a).trans ha) with ⟨ n, rfl ⟩
  norm_cast at ha hb
  use n

@[simp]
lemma Nat.image_cast_int_Ioc (a b:ℕ) : (↑) '' (Set.Ioc a b) = Set.Ioc (a:ℤ) (b:ℤ)  := by
  ext x
  simp
  constructor
  . rintro ⟨ n, ⟨ ha, hb⟩, rfl ⟩
    norm_cast
  rintro ⟨ ha, hb ⟩
  rcases Int.eq_ofNat_of_zero_le ((Int.zero_le_ofNat a).trans (le_of_lt ha)) with ⟨ n, rfl ⟩
  norm_cast at ha hb
  use n

@[simp]
lemma Nat.image_cast_int_Ioo (a b:ℕ) : (↑) '' (Set.Ioo a b) = Set.Ioo (a:ℤ) (b:ℤ) := by
  ext x
  simp
  constructor
  . rintro ⟨ n, ⟨ ha, hb⟩, rfl ⟩
    norm_cast
  rintro ⟨ ha, hb ⟩
  rcases Int.eq_ofNat_of_zero_le ((Int.zero_le_ofNat a).trans (le_of_lt ha)) with ⟨ n, rfl ⟩
  norm_cast at ha hb
  use n

@[simp]
lemma Nat.image_cast_int_Ici (a:ℕ) : (↑) '' (Set.Ici a) = Set.Ici (a:ℤ) := by
  ext x
  simp
  constructor
  . rintro ⟨ n, ha, rfl ⟩
    norm_cast
  rintro ha
  rcases Int.eq_ofNat_of_zero_le ((Int.zero_le_ofNat a).trans ha) with ⟨ n, rfl ⟩
  norm_cast at ha
  use n

@[simp]
lemma Nat.image_cast_int_Ioi (a:ℕ) : (↑) '' (Set.Ioi a) = Set.Ioi (a:ℤ) := by
  ext x
  simp
  constructor
  . rintro ⟨ n, ha, rfl ⟩
    norm_cast
  rintro ha
  rcases Int.eq_ofNat_of_zero_le ((Int.zero_le_ofNat a).trans (le_of_lt ha)) with ⟨ n, rfl ⟩
  norm_cast at ha
  use n

@[simp]
lemma Nat.image_cast_int_Ico_finset (a b:ℕ) : Finset.image (↑) (Finset.Ico a b) = Finset.Ico (a:ℤ) (b:ℤ) := by
  simp [<-Finset.coe_inj, Finset.coe_image, Finset.coe_Ico]

@[simp]
lemma Nat.image_cast_int_Icc_finset (a b:ℕ) : Finset.image (↑) (Finset.Icc a b) = Finset.Icc (a:ℤ) (b:ℤ) := by
  simp [<-Finset.coe_inj, Finset.coe_image, Finset.coe_Icc]

@[simp]
lemma Nat.image_cast_int_Ioc_finset (a b:ℕ) : Finset.image (↑) (Finset.Ioc a b) = Finset.Ioc (a:ℤ) (b:ℤ) := by
  simp [<-Finset.coe_inj, Finset.coe_image, Finset.coe_Icc]

@[simp]
lemma Nat.image_cast_int_Ioo_finset (a b:ℕ) : Finset.image (↑) (Finset.Ioo a b) = Finset.Ioo (a:ℤ) (b:ℤ) := by
  simp [<-Finset.coe_inj, Finset.coe_image, Finset.coe_Ico]


end nat_to_int

section discretize

noncomputable def Set.discretize (I: Set ℝ) : Finset ℤ := (((↑): ℤ → ℝ)⁻¹' I).toFinset'

lemma Set.discretize_mono {I J: Set ℝ} (h: I ⊆  J) (hbound: OrdBounded J) : I.discretize ⊆ J.discretize := by
  simp [Set.discretize, Set.toFinset'_of_set_finite (Real.finite_of_discretized_of_bounded hbound), Set.toFinset'_of_set_finite (Real.finite_of_discretized_of_bounded (OrdBounded.mono h hbound)), preimage_mono h]

lemma Set.discretize_mem {I: Set ℝ} (hbound: OrdBounded I) (n:ℤ) : n ∈ I.discretize ↔ (n:ℝ) ∈ I := by
  rw [discretize, Set.mem_toFinset'_of_set_finite (Real.finite_of_discretized_of_bounded hbound) n,mem_preimage]

@[simp]
lemma Set.discretize_Ico {a b:ℝ}: (Set.Ico a b).discretize = Finset.Ico ⌈ a ⌉ ⌈ b ⌉ := by
  simp [Set.discretize]

@[simp]
lemma Set.discretize_Icc {a b:ℝ}: (Set.Icc a b).discretize = Finset.Icc ⌈ a ⌉ ⌊ b ⌋ := by
  simp [Set.discretize]

@[simp]
lemma Set.discretize_Ioo {a b:ℝ}: (Set.Ioo a b).discretize = Finset.Ioo ⌊ a ⌋ ⌈ b ⌉ := by
  simp [Set.discretize]

@[simp]
lemma Set.discretize_Ioc {a b:ℝ}: (Set.Ioc a b).discretize = Finset.Ioc ⌊ a ⌋ ⌊ b ⌋ := by
  simp [Set.discretize]

lemma Set.discretize_Ico_nonneg {a b:ℝ} (ha: 0
≤ a) (hb: 0 ≤ b): (Set.Ico a b).discretize = Finset.image ((↑) : ℕ → ℤ) (Finset.Ico ⌈ a ⌉₊ ⌈ b ⌉₊) := by
  simp [Nat.cast_ceil_eq_int_ceil ha, Nat.cast_ceil_eq_int_ceil hb]

lemma Set.discretize_Icc_nonneg {a b:ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b): (Set.Icc a b).discretize = Finset.image ((↑) : ℕ → ℤ) (Finset.Icc ⌈ a ⌉₊ ⌊ b ⌋₊) := by
  simp [Nat.cast_ceil_eq_int_ceil ha, Nat.cast_floor_eq_int_floor hb]

lemma Set.discretize_Ioc_nonneg {a b:ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b): (Set.Ioc a b).discretize = Finset.image ((↑) : ℕ → ℤ) (Finset.Ioc ⌊ a ⌋₊ ⌊ b ⌋₊) := by
  simp [Nat.cast_floor_eq_int_floor ha, Nat.cast_floor_eq_int_floor hb]

lemma Set.discretize_Ioo_nonneg {a b:ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b): (Set.Ioo a b).discretize = Finset.image ((↑) : ℕ → ℤ) (Finset.Ioo ⌊ a ⌋₊ ⌈ b ⌉₊) := by
  simp [Nat.cast_floor_eq_int_floor ha, Nat.cast_ceil_eq_int_ceil hb]



end discretize
