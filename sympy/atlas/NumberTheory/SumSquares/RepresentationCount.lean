/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean -/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Card

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval

/-!
# Ordered signed sums of squares
Ordered signed integer vectors and their representation numbers.
-/

namespace SumSquares

/-- Set of ordered signed integer vectors with squared norm `n`. -/
def solutions (k n : ℕ) : Set (Fin k → ℤ) :=
  { x | dotProduct x x = (n : ℤ) }

/-- Number of ordered signed representations of `n` as `k` squares. -/
noncomputable def representationNumber (k n : ℕ) : ℕ :=
  (solutions k n).ncard

@[simp]
theorem mem_solutions {k n : ℕ} {x : Fin k → ℤ} :
    x ∈ solutions k n ↔ dotProduct x x = (n : ℤ) :=
  Iff.rfl

/-- For fixed dimension and norm, there are finitely many ordered signed
integer vectors having that squared norm. -/
theorem solutions_finite (k n : ℕ) : Set.Finite (solutions k n) := by
  apply (Set.Finite.pi fun _ => Set.finite_Icc (-(n : ℤ)) (n : ℤ)).subset
  intro x hx
  rw [Set.mem_pi]
  intro i _
  rw [Set.mem_Icc]
  have hsq : x i ^ 2 ≤ (n : ℤ) := by
    rw [← (mem_solutions.mp hx)]
    simpa only [dotProduct, pow_two] using
      Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (x j))
        (Finset.mem_univ i)
  have habs : |x i| ≤ (n : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Int.natAbs_le_self_sq (x i)).trans hsq
  exact abs_le.mp habs

/-- The representation number is the cardinality of the finite solution set. -/
theorem representationNumber_eq_toFinset_card (k n : ℕ) :
    representationNumber k n = (solutions_finite k n).toFinset.card := by
  exact Set.ncard_eq_toFinset_card _ _

/-- The zero vector has squared norm `0`. -/
theorem zero_mem_solutions (k : ℕ) :
    (0 : Fin k → ℤ) ∈ solutions k 0 := by
  simp [mem_solutions, dotProduct]

theorem zero_notMem_solutions_succ (k n : ℕ) :
    (0 : Fin k → ℤ) ∉ solutions k (n + 1) := by
  simp only [mem_solutions]
  intro h
  have h0 : dotProduct (0 : Fin k → ℤ) (0 : Fin k → ℤ) = 0 := by
    simp [dotProduct]
  rw [h0] at h
  have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  exact hne h.symm

@[simp]
theorem neg_mem_iff {k n : ℕ} {x : Fin k → ℤ} :
    (-x) ∈ solutions k n ↔ x ∈ solutions k n := by
  simp [mem_solutions, neg_dotProduct, dotProduct_neg]

/-- The `k = 0` level set at `n = 0` is universal. -/
theorem solutions_zero_zero : solutions 0 0 = Set.univ := by
  ext x
  simp [mem_solutions, dotProduct]

/-- The `k = 0` level set at positive `n` is empty. -/
theorem solutions_zero_succ (n : ℕ) : solutions 0 (n + 1) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, mem_solutions, iff_false]
  intro h
  have h0 : dotProduct x x = 0 := by
    simp [dotProduct]
  have heq : ((n + 1 : ℕ) : ℤ) = 0 := by
    calc ((n + 1 : ℕ) : ℤ) = dotProduct x x := h.symm
      _ = 0 := h0
  have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  exact hne heq

/-- The `k = 1` level set at `n = 0` is the zero singleton. -/
theorem solutions_one_zero : solutions 1 0 = {(0 : Fin 1 → ℤ)} := by
  ext x
  simp only [mem_solutions, Set.mem_singleton_iff]
  have hDot : dotProduct x x = x (0 : Fin 1) * x 0 := by
    simp only [dotProduct]
    have hU : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim _ _
    rw [hU, Finset.sum_singleton]
  rw [hDot]
  have hx : x = (0 : Fin 1 → ℤ) ↔ x (0 : Fin 1) = 0 := by
    constructor
    · intro h
      exact congr_fun h 0
    · intro h0
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      rw [hi, h0, Pi.zero_apply]
  rw [hx]
  simp [mul_eq_zero]

/-- The representation number at `k = 0, n = 0` is one. -/
theorem representationNumber_zero_zero : representationNumber 0 0 = 1 := by
  simp [representationNumber, solutions_zero_zero, Set.ncard_univ]

/-- The representation number at `k = 0` and positive `n` is zero. -/
theorem representationNumber_zero_succ (n : ℕ) :
    representationNumber 0 (n + 1) = 0 := by
  simp [representationNumber, solutions_zero_succ]

/-- The representation number at `k = 1, n = 0` is one. -/
theorem representationNumber_one_zero : representationNumber 1 0 = 1 := by
  simp [representationNumber, solutions_one_zero]

end SumSquares
