import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[pell_riordan_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellRiordan.lean)
-/
@[path]
lemma pell_riordan_general
  :
-- imply
  (k : ℕ) (p : ℕ → ℕ → ℕ)
    (hgen : ∀ n : ℕ,
    PowerSeries.mk (fun m => (↑(p n m) : ℚ)) * (1 - PowerSeries.X (R := by
-- proof
  have hA : IsUnit (1 - PowerSeries.X (R := ℚ)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hAm : IsUnit ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) := hA.pow (m + 1)
  have hP : PowerSeries.mk (fun j => (↑(p m j) : ℚ)) =
    (Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i)) ^ m *
      Ring.inverse ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) := by
    have h := hgen m
    calc PowerSeries.mk (fun j => (↑(p m j) : ℚ))
      = PowerSeries.mk (fun j => (↑(p m j) : ℚ)) * 1 := by rw [mul_one]
      _ = PowerSeries.mk (fun j => (↑(p m j) : ℚ)) *
        (((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) *
          Ring.inverse ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1))) := by
        rw [Ring.mul_inverse_cancel _ hAm]
      _ = (PowerSeries.mk (fun j => (↑(p m j) : ℚ)) *
        ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1))) *
        Ring.inverse ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) := by rw [mul_assoc]
      _ = (Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i)) ^ m *
        Ring.inverse ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) := by rw [h]
  have hInv : Ring.inverse ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) =
    (Ring.inverse (1 - PowerSeries.X (R := ℚ))) ^ (m + 1) := by
    rw [← Ring.inverse_pow]
  have hRHS : Ring.inverse (1 - PowerSeries.X (R := ℚ)) *
    (PowerSeries.X (R := ℚ) *
      Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i) *
      Ring.inverse (1 - PowerSeries.X (R := ℚ))) ^ m =
    PowerSeries.X (R := ℚ) ^ m * PowerSeries.mk (fun j => (↑(p m j) : ℚ)) := by
    have hring : Ring.inverse (1 - PowerSeries.X (R := ℚ)) *
      (PowerSeries.X (R := ℚ) *
        Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i) *
        Ring.inverse (1 - PowerSeries.X (R := ℚ))) ^ m =
      PowerSeries.X (R := ℚ) ^ m *
        ((Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i)) ^ m *
          (Ring.inverse (1 - PowerSeries.X (R := ℚ))) ^ (m + 1)) := by ring
    rw [hring, ← hInv, ← hP]
  rw [hRHS, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk]
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pell_riordan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellRiordan.lean)
-/
@[path]
lemma pell_riordan
  :
-- imply
  ∀ (k : ℕ) (hk : 2 ≤ k) (p : ℕ → ℕ → ℕ)
    (hgen : ∀ n : ℕ,
    PowerSeries.mk (fun m => (↑(p n m) : ℚ)) * (1 - PowerSeries.X (R := by
-- proof
  intro k _ p hgen n m
  exact pell_riordan_general k p hgen n m

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
