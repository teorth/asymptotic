import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Order.MinMax
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace Asymptotics

variable {E : Type*} [SeminormedAddCommGroup E]
variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable {k : Type*} [NormedField k]

def Ll (C:NNReal) (X:E) (Y:ℝ) : Prop := ‖X‖ ≤ C * Y

notation:10 X " ≪[" C "] " Y => Ll C X Y

@[simp]
lemma ll_def (C:NNReal) (X:E) (Y:ℝ) : (X ≪[C] Y) ↔ (‖X‖ ≤ C * Y) := by rfl

lemma isBigOWith_iff_ll {α : Type*} {C : NNReal} {l : Filter α} {X : α → E} {Y : α → ℝ} (hY: ∀ x, 0 ≤ Y x): IsBigOWith C l X Y ↔ ∀ᶠ x in l, X x ≪[C] Y x := by
  simp
  rw [IsBigOWith_def]
  apply iff_of_eq
  congr with x
  simp
  rw [abs_of_nonneg (hY x)]

private lemma real_le_nnreal (x:ℝ) : ∃ (y:NNReal), x ≤ y := by
  use (max 1 x).toNNReal
  rw [Real.coe_toNNReal _ (le_max_of_le_left zero_le_one)]
  exact le_max_right 1 x

lemma isBigO_iff_ll {α : Type*} (l : Filter α) (X : α → E) (Y : α → ℝ) (hY: ∀ x, 0 ≤ Y x) : X =O[l] Y ↔ ∃ (C:NNReal), ∀ᶠ x in l, X x ≪[C] Y x := by
  rw [IsBigO_def]
  constructor
  . rintro ⟨ c, hc ⟩
    rw [Asymptotics.isBigOWith_iff] at hc
    rcases real_le_nnreal c with ⟨ C, hC ⟩
    use C
    apply Filter.Eventually.mono hc
    intro x hx
    simp [abs_of_nonneg (hY x)] at hx ⊢
    apply hx.trans
    exact mul_le_mul_of_nonneg_right hC (hY x)
  rintro ⟨ C, h ⟩
  rw [<-isBigOWith_iff_ll hY] at h
  use C


lemma nonneg_of_ll {C:NNReal} (hC: C ≠ 0) {X:E} {Y:ℝ} (h: X ≪[C] Y) : 0 ≤ Y  := by
  simp at h
  replace h := (norm_nonneg X).trans h
  have : 0 < C := zero_lt_iff.mpr hC
  rw [<-mul_le_mul_left (a := (C:ℝ))]
  . simpa
  norm_cast

lemma ll_of_le {X:E} {Y:ℝ} (h: ‖X‖ ≤ Y) : X ≪[1] Y := by simp [h]

lemma ll_abs (X:E) : X ≪[1] ‖X‖ := by simp

lemma ll_refl {X:ℝ} (hX: 0 ≤ X) : X ≪[1] X := by simp [abs_of_nonneg hX]

lemma norm_ll_iff (C:NNReal) (X:E) (Y:ℝ) : (X ≪[C] Y) ↔ (‖X‖ ≪[C] Y) := by
  simp

lemma ll_trans {C₁ C₂:NNReal} (hC₁: C₁ ≠ 0) {X:E} {Y Z:ℝ} (hXY: X ≪[C₁] Y) (hYZ: Y ≪[C₂] Z) : X ≪[C₁*C₂] Z := by
  simp [abs_of_nonneg (nonneg_of_ll hC₁ hXY)] at hXY hYZ ⊢
  apply hXY.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hYZ (NNReal.coe_nonneg C₁)

lemma ll_of_ll_of_le {C:NNReal} {X:E} {Y Z:ℝ} (hXY: X ≪[C] Y) (hYZ: Y ≤ Z) : X ≪[C] Z := by
  simp at hXY ⊢
  apply hXY.trans
  exact mul_le_mul_of_nonneg_left hYZ (NNReal.coe_nonneg C)

lemma ll_of_le_of_ll {C:NNReal} {X:E} {Y Z:ℝ} (hXY: ‖X‖ ≤ Y) (hYZ: Y ≪[C] Z) : X ≪[C] Z := by
  convert ll_trans one_ne_zero (ll_of_le hXY) hYZ
  exact (one_mul C).symm

lemma ll_of_le_of_ll' {C:NNReal} {X Y Z:ℝ} (hX: 0 ≤ X) (hXY: X ≤ Y) (hYZ: Y ≪[C] Z) : X ≪[C] Z := by
  apply ll_of_le_of_ll _ hYZ
  simp [abs_of_nonneg hX, hXY]

lemma ll_increase_const {C₁ C₂:NNReal} (hC₁: C₁ ≠ 0) {X:E} {Y:ℝ} (hXY : X ≪[C₁] Y) (hC : C₁ ≤ C₂) : X ≪[C₂] Y := hXY.trans (mul_le_mul_of_nonneg_right hC (nonneg_of_ll hC₁ hXY))

lemma ll_absorb_const {C₁ C₃:NNReal} (hC₁: C₁ ≠ 0) {C₂:ℝ} (hC₂: 0 < C₂) (hC: C₁ * C₂ ≤ C₃) {X:E} (Y:ℝ) (hXY: X ≪[C₁] C₂*Y) : X ≪[C₃] Y := by
  have := nonneg_of_ll hC₁ hXY
  simp at hXY ⊢
  apply hXY.trans
  rw [<-mul_assoc]
  apply mul_le_mul_of_nonneg_right hC
  rw [<-mul_le_mul_left (a := (C₂:ℝ))]
  . simpa
  norm_cast

lemma neg_ll {C: NNReal} {X:E} (Y:ℝ) : (X ≪[C] Y) ↔ ((-X) ≪[C] Y) := by
  simp

lemma add_ll {C₁ C₂:NNReal} {X₁ X₂:E} (Y:ℝ) (h1: X₁ ≪[C₁] Y) (h2: X₂ ≪[C₂] Y) : X₁ + X₂ ≪[C₁ + C₂] Y := by
  simp at h1 h2 ⊢
  apply (norm_add_le X₁ X₂).trans
  convert add_le_add h1 h2 using 1
  ring

lemma add_ll_add {C₁ C₂:NNReal} (hC₁: C₁ ≠ 0) (hC₂: C₂ ≠ 0) {X₁ X₂:E} {Y₁ Y₂:ℝ} (h1: X₁ ≪[C₁] Y₁) (h2: X₂ ≪[C₂] Y₂) : X₁ + X₂ ≪[max C₁ C₂] Y₁ + Y₂ := by
  simp at h1 h2 ⊢
  apply (norm_add_le X₁ X₂).trans
  apply (add_le_add h1 h2).trans
  rw [mul_add]
  apply add_le_add
  . exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (nonneg_of_ll hC₁ h1)
  exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (nonneg_of_ll hC₂ h2)

lemma add_ll_add' {C:NNReal} (hC: C ≠ 0) {X₁ X₂:E} {Y₁ Y₂:ℝ} (h1: X₁ ≪[C] Y₁) (h2: X₂ ≪[C] Y₂) : X₁ + X₂ ≪[C] Y₁ + Y₂ := by
  convert add_ll_add hC hC h1 h2
  exact (max_self C).symm

lemma sub_ll {C₁ C₂:NNReal} {X₁ X₂:E} (Y:ℝ) (h1: X₁ ≪[C₁] Y) (h2: X₂ ≪[C₂] Y) : X₁ - X₂ ≪[C₁ + C₂] Y := by
  simp at h1 h2 ⊢
  apply (norm_sub_le X₁ X₂).trans
  convert add_le_add h1 h2 using 1
  ring

lemma sub_ll_add {C₁ C₂:NNReal} (hC₁: C₁ ≠ 0) (hC₂: C₂ ≠ 0) {X₁ X₂:E} {Y₁ Y₂:ℝ} (h1: X₁ ≪[C₁] Y₁) (h2: X₂ ≪[C₂] Y₂) : X₁ - X₂ ≪[max C₁ C₂] Y₁ + Y₂ := by
  rw [ll_def] at h1 h2 ⊢
  apply (norm_sub_le X₁ X₂).trans
  apply (add_le_add h1 h2).trans
  rw [mul_add]
  apply add_le_add
  . exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (nonneg_of_ll hC₁ h1)
  exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (nonneg_of_ll hC₂ h2)

lemma sub_ll_add' {C:NNReal} (hC: C ≠ 0) {X₁ X₂:E} {Y₁ Y₂:ℝ} (h1: X₁ ≪[C] Y₁) (h2: X₂ ≪[C] Y₂) : X₁ - X₂ ≪[C] Y₁ + Y₂ := by
  convert sub_ll_add hC hC h1 h2
  exact (max_self C).symm

lemma mul_ll_mul {C₁ C₂:NNReal} (hC₁: C₁ ≠ 0) {X₁ X₂:k} {Y₁ Y₂:ℝ} (h1: X₁ ≪[C₁] Y₁) (h2: X₂ ≪[C₂] Y₂) : X₁*X₂ ≪[C₁ * C₂] Y₁ * Y₂ := by
  have := nonneg_of_ll hC₁ h1;
  simp at h1 h2 ⊢
  convert mul_le_mul h1 h2 (norm_nonneg _) (by positivity) using 1
  ring

lemma smul_ll_mul {C₁ C₂:NNReal} (hC₁: C₁ ≠ 0)  {a:ℝ} {X:V} {Y Z:ℝ} (h1: a ≪[C₁] Y) (h2: X ≪[C₂] Z) : a • X ≪[C₁ * C₂] Y * Z := by
  have := nonneg_of_ll hC₁ h1
  simp at h1 h2 ⊢
  rw [norm_smul]
  convert mul_le_mul h1 h2 (norm_nonneg _) (by positivity) using 1
  ring

lemma mul_ll_mul_left {C:NNReal} (hC: C ≠ 0) {X:k} {Y:ℝ} (h: X ≪[C] Y) (a:k): a*X ≪[C] ‖a‖ * Y := by
  apply ll_increase_const _ _ (show 1*C ≤ C by simp)
  . simp [hC]
  exact mul_ll_mul one_ne_zero (ll_abs a) h

lemma smul_ll_mul_left {C:NNReal} (hC: C ≠ 0) {X:V} {Y:ℝ} (h: X ≪[C] Y) (a:ℝ): a • X ≪[C] ‖a‖ * Y := by
  apply ll_increase_const _ _ (show 1*C ≤ C by simp)
  . simp [hC]
  exact smul_ll_mul one_ne_zero (ll_abs a) h

lemma mul_ll_mul_right {C:NNReal} (hC: C ≠ 0) {X:k} {Y:ℝ} (h: X ≪[C] Y) (a:k) : X*a ≪[C] Y * ‖a‖ := by
  rw [mul_comm X _, mul_comm Y _]
  exact mul_ll_mul_left hC h a

lemma max_ll_add {Y₁ Y₂:ℝ} (hY₁: 0 ≤ Y₁) (hY₂: 0 ≤ Y₂) : max Y₁ Y₂ ≪[1] Y₁ + Y₂ := by
  simp [abs_of_nonneg (show 0 ≤ max Y₁ Y₂ by positivity)]
  exact ⟨hY₂, hY₁⟩

lemma add_ll_max {Y₁ Y₂:ℝ} (hY₁: 0 ≤ Y₁) (hY₂: 0 ≤ Y₂) : Y₁ + Y₂ ≪[2] max Y₁ Y₂ := by
  simp [abs_of_nonneg (show 0 ≤ Y₁ + Y₂ by positivity)]
  rcases le_or_gt Y₁ Y₂ with h | h
  . simp [h]; linarith
  simp [le_of_lt h]; linarith

open BigOperators MeasureTheory

lemma sum_ll_sum {C:NNReal} {Ω :Type*} {S: Finset Ω} {X: Ω → E} {Y: Ω → ℝ} (h: ∀ s ∈ S, X s ≪[C] Y s) : (∑ s in S, X s) ≪[C] ∑ s in S, Y s := by
  simp at h ⊢
  rw [Finset.mul_sum]
  exact (norm_sum_le S X).trans (Finset.sum_le_sum h)

lemma tsum_ll_tsum {C:NNReal} {Ω :Type*} [CompleteSpace E] {X: Ω → E} {Y: Ω → ℝ} (h: ∀ s, X s ≪[C] Y s) (hsum: Summable Y): Summable X ∧ ((∑' s, X s) ≪[C] ∑' s, Y s) := by
  simp at h ⊢
  have : Summable (fun s ↦ ‖X s‖ ) := by
    apply Summable.of_norm_bounded (fun s ↦ C * (Y s)) (Summable.mul_left (C:ℝ) hsum)
    simp [h]
  constructor
  . exact Summable.of_norm this
  apply (norm_tsum_le_tsum_norm this).trans
  rw [<-tsum_mul_left]
  exact tsum_le_tsum h this (Summable.mul_left (C:ℝ) hsum)

lemma integ_ll_integ  {C:NNReal} {Ω :Type*}  [MeasurableSpace Ω] (μ: Measure Ω := by volume_tac) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {X: Ω → V} {Y: Ω → ℝ} (h: ∀ᵐ s ∂ μ, X s ≪[C] Y s) (hinteg: Integrable Y μ) (hmes: AEStronglyMeasurable X μ): Integrable X μ ∧ (∫ s, X s ∂ μ ≪[C] ∫ s, Y s ∂ μ) := by
  constructor
  . apply Integrable.mono' (Integrable.const_mul hinteg C) hmes
    simp at h
    exact h
  simp at h ⊢
  rw [<- MeasureTheory.integral_mul_left]
  exact norm_integral_le_of_norm_le (Integrable.const_mul hinteg C) h

/-- missing from Mathlib -/
theorem nullMeasurableSet_le {α : Type*} {δ : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [MeasurableSpace δ] [LinearOrder α] [OrderClosedTopology α] [SecondCountableTopology α] {μ : MeasureTheory.Measure δ} {f : δ → α} {g : δ → α} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : NullMeasurableSet { a | f a ≤ g a } μ :=
  (hf.prod_mk hg).nullMeasurable measurableSet_le'

lemma integ_ll_integ_set  {C:NNReal} {Ω :Type*}  [MeasurableSpace Ω] (μ: Measure Ω := by volume_tac) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {E: Set Ω} {X: Ω → V} {Y: Ω → ℝ} (h: ∀ᵐ s ∂ μ, s ∈ E → (X s ≪[C] Y s)) (hinteg: IntegrableOn Y E μ) (hmes: AEStronglyMeasurable X (Measure.restrict μ E)): IntegrableOn X E μ ∧ (∫ s in E, X s ∂ μ ≪[C] ∫ s in E, Y s ∂ μ) := by
  convert integ_ll_integ (Measure.restrict μ E) (X := X) (Y := Y) ?_ hinteg hmes using 1
  rwa [MeasureTheory.ae_restrict_iff₀]
  simp
  apply nullMeasurableSet_le _ _
  . exact AEStronglyMeasurable.aemeasurable (Continuous.comp_aestronglyMeasurable (Continuous.norm continuous_id') hmes)
  exact AEStronglyMeasurable.aemeasurable ( AEStronglyMeasurable.const_mul (Integrable.aestronglyMeasurable hinteg) C)


notation:10 X " =[" C "] " Y " + O(" Z ")" => Ll C (X-Y) Z


lemma eqPlusBigO_def (C:NNReal) (X Y:E) (Z:ℝ) : (X =[C] Y + O(Z)) ↔ (X-Y ≪[C] Z) := by rfl

lemma eqPlusBigO_def' (C:NNReal) (X Y:E) (Z:ℝ) : (X =[C] Y + O(Z)) ↔ (‖X-Y‖ ≪[C] Z) := by simp

lemma eqPlusBigO_iff_le_and_ge (C:NNReal) (X Y:ℝ) : (X =[C] Y + O(Z)) ↔ (X ≤ Y + C*Z ∧ X ≥ Y - C*Z) := by
  simp [abs_le]
  rw [add_comm (C*Z) Y]
  exact and_comm

lemma eqPlusBigO_rfl (C:NNReal) (X:E) {Z:ℝ} (hZ: 0 ≤ Z) : (X =[C] X + O(Z)) := by
  simp; positivity

lemma eqPlusBigO_symm (C:NNReal) (X Y:E) {Z:ℝ} : (X =[C] Y + O(Z)) ↔ (Y =[C] X + O(Z)) := by
  simp [<-dist_eq_norm_sub]
  rw [dist_comm]

lemma eqPlusBigO_trans {C C':NNReal} {X Y Z:E} {W:ℝ} (h: X =[C] Y + O(W)) (h': Y =[C'] Z + O(W)) : (X =[C+C'] Z + O(W)) := by
  simp [<-dist_eq_norm_sub] at h h' ⊢
  apply (dist_triangle X Y Z).trans
  convert add_le_add h h' using 1
  ring

lemma eqPlusBigO_trans' {C C':NNReal} (hC: C ≠ 0) (hC': C' ≠ 0) {X Y Z:E} {W W':ℝ} (h: X =[C] Y + O(W)) (h': Y =[C'] Z + O(W')) : (X =[max C C'] Z + O(W + W')) := by
  rw [eqPlusBigO_def', <-dist_eq_norm_sub] at h h' ⊢
  exact ll_of_le_of_ll' (dist_nonneg) (dist_triangle X Y Z) (add_ll_add hC hC' h h')

lemma eqPlusBigO_of_zero (C:NNReal) (X:E) {Y:ℝ} : (X =[C] 0 + O(Y)) ↔ (X ≪[C] Y) := by
  rw [sub_zero]

lemma eqPlusBigO_increase_const {C₁ C₂:NNReal} (hC₁: C₁ ≠ 0) {X Y:E} {Z:ℝ} (hXY : X=[C₁] Y + O(Z)) (hC : C₁ ≤ C₂) : X =[C₂] Y + O(Z) := ll_increase_const hC₁ hXY hC

lemma eqPlusBigO_of_ll {C₁ C₂: NNReal} (hC₁: C₁ ≠ 0) (X:E) {Y:E} {Z Z':ℝ} (h: X =[C₁] Y + O(Z)) (h': Z ≪[C₂] Z'): X =[C₁*C₂] Y + O(Z') := ll_trans hC₁ h h'

lemma eqPlusBigO_of_le {C: NNReal} (X:E) {Y:E} {Z Z':ℝ} (h: X =[C] Y + O(Z)) (h': Z ≤ Z'): X =[C] Y + O(Z') := ll_of_ll_of_le h h'

lemma add_eqPlusBigO {C: NNReal} (X:E) {Y:E} {Z:ℝ} (h: Y ≪[C] Z) : X + Y =[C] X + O(Z) := by
  simp at h ⊢
  exact h

lemma sub_eqPlusBigO {C: NNReal} (X:E) {Y:E} {Z:ℝ} (h: Y ≪[C] Z) : X - Y =[C] X + O(Z) := by
  simp at h ⊢
  exact h

lemma neg_of_eqPlusBigO  {C:NNReal} {X Y: E} {Z:ℝ} (h: X =[C] Y + O(Z)) : -X =[C] -Y + O(Z) := by
  rw [neg_ll] at h
  convert h using 1
  abel

lemma add_of_eqPlusBigO {C:NNReal} {X Y X' Y': E} {Z Z':ℝ} (h: X =[C] Y + O(Z)) (h': X' =[C] Y' + O(Z')) : X + X' =[C] Y+Y' + O(Z+Z') := by
  rw [ll_def] at h h' ⊢
  rw [(show X+X' - (Y+Y') = (X-Y)+(X'-Y') by abel), (show C * (Z + Z') = C*Z + C*Z' by ring)]
  exact LE.le.trans (norm_add_le _ _) (add_le_add h h')

lemma sub_of_eqPlusBigO {C:NNReal} {X Y X' Y': E} {Z Z':ℝ} (h: X =[C] Y + O(Z)) (h': X' =[C] Y' + O(Z')) : X - X' =[C] Y-Y' + O(Z+Z') := by
  rw [ll_def] at h h' ⊢
  rw [(show X-X' - (Y-Y') = (X-Y)-(X'-Y') by abel), (show C * (Z + Z') = C*Z + C*Z' by ring)]
  apply LE.le.trans (norm_sub_le _ _) (add_le_add h h')

lemma sum_of_eqPlusBigO {C:NNReal} {Ω :Type*} {S: Finset Ω} {X Y: Ω → E} {Z: Ω → ℝ} (h: ∀ s ∈ S, X s=[C] Y s + O(Z s)) : (∑ s in S, X s) =[C] ∑ s in S, Y s + O(∑ s in S, Z s):= by
  rw [eqPlusBigO_def', <-Finset.sum_sub_distrib, <-norm_ll_iff]
  apply sum_ll_sum h

lemma int_of_eqPlusBigO {C:NNReal} {Ω :Type*} [MeasurableSpace Ω]  (μ: Measure Ω := by volume_tac) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {S: Set Ω} {X Y: Ω → V} {Z: Ω → ℝ} (h: ∀ᵐ s ∂ μ, s ∈ S → (X s =[C] Y s + O(Z s))) (hinteg: IntegrableOn Z S μ) (hXmes : AEStronglyMeasurable X (Measure.restrict μ S)) (hYinteg : IntegrableOn Y S μ): (∫ s in S, X s ∂ μ) =[C] ∫ s in S, Y s ∂ μ + O(∫ s in S, Z s ∂ μ):= by
  have := integ_ll_integ_set μ h hinteg (AEStronglyMeasurable.sub hXmes  ((integrable_def Y (Measure.restrict μ S)).mp hYinteg).1)
  rw [eqPlusBigO_def, <-integral_sub]
  convert this.2
  . convert Integrable.add this.1 hYinteg
    ext s
    simp
  exact hYinteg

lemma mul_eqPlusBigO_mul {C₁ C₂:NNReal} (hC₁: C₁ ≠ 0) (hC₂: C₂ ≠ 0) {X₁ X₂ Y₁ Y₂:k} {Z₁ Z₂ W₁ W₂:ℝ} (h1: X₁ =[C₁] Y₁ + O(Z₁)) (h2: X₂ =[C₂] Y₂ + O(Z₂)) (h1': Y₁ ≪[C₁] W₁) (h2': Y₂ ≪[C₂] W₂) : X₁*X₂ =[C₁*C₂] Y₁ * Y₂ + O(Z₁*W₂+W₁*Z₂+Z₁*Z₂):= by
  have : X₁*X₂ - Y₁*Y₂ = (X₁-Y₁)*Y₂ + Y₁*(X₂-Y₂) + (X₁-Y₁)*(X₂-Y₂) := by ring
  rw [this]
  have hC: C₁ * C₂ ≠ 0 := mul_ne_zero hC₁ hC₂
  apply add_ll_add' hC (add_ll_add' hC _ _) _
  . exact mul_ll_mul hC₁ h1 h2'
  . exact mul_ll_mul hC₁ h1' h2
  . apply mul_ll_mul hC₁ h1 h2

lemma mul_eqPlusBigO_mul_left {C:NNReal} (hC: C ≠ 0) {X Y:k} {Z:ℝ} (h: X =[C] Y + O(Z)) (a:k): a*X =[C] a*Y + O(‖a‖ * Z) := by
  convert mul_ll_mul_left hC h a using 1
  exact (mul_sub a X Y).symm

lemma smul_eqPlusBigO_mul_left {C:NNReal} (hC: C ≠ 0) {X Y:V} {Z:ℝ} (h: X =[C] Y + O(Z)) (a:ℝ): a • X =[C] a • Y + O(‖a‖ * Z) := by
  convert smul_ll_mul_left hC h a using 1
  exact (smul_sub a X Y).symm

lemma mul_eqPlusBigO_mul_right {C:NNReal} (hC: C ≠ 0) {X Y:k} {Z:ℝ} (h: X =[C] Y + O(Z)) (a:k): X*a =[C] Y*a + O(Z * ‖a‖) := by
  convert mul_ll_mul_right hC h a using 1
  exact (sub_mul X Y a).symm
