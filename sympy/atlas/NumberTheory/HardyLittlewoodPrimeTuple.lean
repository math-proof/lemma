/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HardyLittlewoodPrimeTuple.lean -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Hardy–Littlewood prime-tuple data

Reusable definitions from the Hardy–Littlewood prime-tuple conjecture block
(statement `jis_43e1aedfa0e84467b1f1765e`, concept `jis_sem_c814202d5e6a0edd6fed8bb5`).

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Miller/miller8.tex>.
-/

open scoped BigOperators

namespace MetaMathlibExt

/-- Number of distinct residues of the tuple `b` modulo `p`, i.e. the source's
`v_p(b)` (statement `jis_43e1aedfa0e84467b1f1765e`, concept `jis_sem_c814202d5e6a0edd6fed8bb5`). -/
def hardyLittlewoodResidueCount (m : ℕ) (b : Fin m → ℤ) (p : ℕ) : ℕ :=
  (Finset.univ.image (fun i => (b i) % (p : ℤ))).card

/-- Admissibility of the tuple `b`: `v_p(b) ≠ p` for every prime `p`
(statement `jis_43e1aedfa0e84467b1f1765e`, concept `jis_sem_c814202d5e6a0edd6fed8bb5`). -/
def IsHardyLittlewoodAdmissible (m : ℕ) (b : Fin m → ℤ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → hardyLittlewoodResidueCount m b p ≠ p

/-- The source's `P(x; b)`: number of integers `1 ≤ n ≤ x` for which every
`n + bᵢ` is (a natural) prime
(statement `jis_43e1aedfa0e84467b1f1765e`, concept `jis_sem_c814202d5e6a0edd6fed8bb5`). -/
noncomputable def hardyLittlewoodPrimeTupleCount (m : ℕ) (b : Fin m → ℤ) (x : ℕ) : ℕ :=
  Set.ncard { n : ℕ | 1 ≤ n ∧ n ≤ x ∧ ∀ i, ∃ q : ℕ, Nat.Prime q ∧ (n : ℤ) + b i = (q : ℤ) }

/-- Euler factor `(p / (p - 1)) ^ (m - 1) * ((p - v_p(b)) / (p - 1))` of the
singular series (statement `jis_43e1aedfa0e84467b1f1765e`,
concept `jis_sem_c814202d5e6a0edd6fed8bb5`). -/
noncomputable def hardyLittlewoodEulerFactor (m : ℕ) (b : Fin m → ℤ) (p : ℕ) : ℝ :=
  ((p : ℝ) / ((p : ℝ) - 1)) ^ (m - 1) *
    (((p : ℝ) - (hardyLittlewoodResidueCount m b p : ℝ)) / ((p : ℝ) - 1))

/-- Singular series `𝔖(b)`: Euler product over all primes of the Euler factors
(statement `jis_43e1aedfa0e84467b1f1765e`, concept `jis_sem_c814202d5e6a0edd6fed8bb5`). -/
noncomputable def hardyLittlewoodSingularSeries (m : ℕ) (b : Fin m → ℤ) : ℝ :=
  ∏' (p : ℕ), (if Nat.Prime p then hardyLittlewoodEulerFactor m b p else 1)

end MetaMathlibExt
