import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Abs
import Mathlib.Algebra.BigOperators.Order

class Nonnegative {α: Type*} [OrderedAddCommMonoid α] (x: α) : Prop
where
  nonneg : 0 ≤ x

lemma nonnegative_of_nonneg {α: Type*} [OrderedAddCommMonoid α] {x:α} (hx: 0 ≤ x) : Nonnegative x where
  nonneg := hx

lemma nonneg {α: Type*} [OrderedAddCommMonoid α] (x:α) [Nonnegative x] : 0 ≤ x := Nonnegative.nonneg

instance {α:Type*} [OrderedSemiring α] {n:ℕ} : Nonnegative (n:α) where
  nonneg := Nat.cast_nonneg n

instance {n:ℤ} [Nonnegative n] : Nonnegative (n:ℚ) where
  nonneg := by norm_cast; exact nonneg n

instance {n:ℚ} [Nonnegative n] : Nonnegative (n:ℝ) where
  nonneg := by norm_cast; exact nonneg n

instance {x:NNReal} : Nonnegative x where
  nonneg := x.2

instance {α: Type*} [OrderedAddCommMonoid α] {x y: α} [hx:Nonnegative x] [hy:Nonnegative y] : Nonnegative (x+y) where
  nonneg := add_nonneg hx.nonneg hy.nonneg

instance {R: Type*} [OrderedSemiring R] {x y: R} [hx:Nonnegative x] [hy:Nonnegative y] : Nonnegative (x*y) where
  nonneg := mul_nonneg hx.nonneg hy.nonneg

instance {k: Type*} [LinearOrderedSemifield k] {x: k} [hx:Nonnegative x] : Nonnegative x⁻¹ where
  nonneg := inv_nonneg.mpr hx.nonneg

instance {k: Type*} [LinearOrderedSemifield k] {x y: k} [hx:Nonnegative x] [hy:Nonnegative y] : Nonnegative (x/y) where
  nonneg := div_nonneg hx.nonneg hy.nonneg

instance {k: Type*} [LinearOrderedSemifield k] {x: k} {n:ℤ} [hx:Nonnegative x] : Nonnegative (x^n) where
  nonneg := zpow_nonneg hx.nonneg n

instance {x: ℝ} {y:ℝ} [hx:Nonnegative x] : Nonnegative (x^y) where
  nonneg := Real.rpow_nonneg_of_nonneg hx.nonneg y


instance {G: Type*} [LinearOrderedAddCommGroup G]
{x: G} : Nonnegative |x| where
  nonneg := abs_nonneg x

instance {x: ℝ} : Nonnegative (Real.sqrt x) where
  nonneg := Real.sqrt_nonneg x

instance {S: Type*} [LinearOrderedRing S] {x: S} : Nonnegative (x^2) where
  nonneg := sq_nonneg x

instance {z: ℂ} : Nonnegative (Complex.abs z) where
  nonneg := by rw [Complex.abs_apply]; exact nonneg _

instance {E : Type*} [SeminormedAddGroup E] (a : E) : Nonnegative ‖a‖ where
  nonneg := norm_nonneg a


@[simp]
lemma abs_of_nonneg' {G: Type*} [LinearOrderedAddCommGroup G] (x:G) [Nonnegative x] : |x| = x := abs_of_nonneg (nonneg x)

@[simp]
lemma toNNReal_of_nonneg' (x:ℝ) [Nonnegative x] : x.toNNReal = x := by
  rw [Real.toNNReal_of_nonneg (nonneg x)]; rfl


lemma mul_le_mul_of_nonneg_right' {s: Type*} [LinearOrderedSemiring s] {a b c:s} [Nonnegative a] (h : b ≤ c) : b * a ≤ c * a := mul_le_mul_of_nonneg_right h (nonneg a)

lemma mul_le_mul_of_nonneg_left' {s: Type*} [LinearOrderedSemiring s] {a b c:s} [Nonnegative a] (h : b ≤ c) : a * b ≤ a * c := mul_le_mul_of_nonneg_left h (nonneg a)


lemma nonnegative_of_finset_sum {α: Type*} [OrderedAddCommMonoid α] {X : Type*} {s: Finset X} {f: X → α} (h: ∀ i ∈ s, Nonnegative (f i)) : Nonnegative (Finset.sum s fun i => f i) := by
  apply nonnegative_of_nonneg (Finset.sum_nonneg _)
  intro i hi
  exact (h i hi).nonneg


--- examples of using the Nonnegative class

example (x y:ℝ) : Nonnegative (x^2 + y^2) := by infer_instance

example (x y:ℝ) : 0 ≤ x^2 + y^2 := nonneg _

example (x:ℝ) : 2 * x^2 - |2*x^2| = 0 := by
  have : Nonnegative (2:ℕ) := by infer_instance
  simp
