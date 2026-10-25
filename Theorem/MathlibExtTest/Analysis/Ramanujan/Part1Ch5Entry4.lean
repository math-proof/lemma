/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch5Entry4.lean -/


import Def.Analysis.Ramanujan.Part1Ch5Entry4
import Lemma.Complex.Part1Ch5Entry4
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 4 API checks

Small rows of the Eulerian triangle, coefficients out of range, `chapter5Psi` at `n = 0` and
`n = 2`, and the entry itself at `n = 0` and `n = 2`.
-/


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry4

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry4

-- Rows `1`, `2` and `3` of the Eulerian triangle: `1`; `1, 1`; `1, 4, 1`.
example : eulerianNumber 1 0 = 1 := by decide

example : eulerianNumber 2 0 = 1 ∧ eulerianNumber 2 1 = 1 := by decide

example : eulerianNumber 3 0 = 1 ∧ eulerianNumber 3 1 = 4 ∧ eulerianNumber 3 2 = 1 := by decide

-- Coefficients at or past the end of a row vanish.
example : eulerianNumber 0 1 = 0 ∧ eulerianNumber 3 3 = 0 ∧ eulerianNumber 3 7 = 0 := by decide

example {R : Type*} [CommRing R] (p : R) : chapter5Psi 0 p = 1 := by simp [chapter5Psi]

example {R : Type*} [CommRing R] (p : R) : chapter5Psi 2 p = 1 - p := by
  simp [chapter5Psi, Finset.sum_range_succ, eulerianNumber]
  ring

-- `n = 0` is the geometric series.
example (p : ℂ) (hp : ‖p‖ < 1) : ∑' k : ℕ, (-p) ^ k = 1 / (p + 1) := by
  obtain ⟨-, -, h⟩ := ramanujan_part1_ch5_entry4 0 p hp
  simpa [chapter5Psi, chapter5Entry4Term] using h.symm

example (p : ℂ) (hp : ‖p‖ < 1) :
    ∑' k : ℕ, ((k : ℂ) + 1) ^ 2 * (-p) ^ k = (1 - p) / (p + 1) ^ 3 := by
  obtain ⟨-, -, h⟩ := ramanujan_part1_ch5_entry4 2 p hp
  have h2 : chapter5Psi 2 p = 1 - p := by
    simp [chapter5Psi, Finset.sum_range_succ, eulerianNumber]
    ring
  rw [h2] at h
  exact h.symm

end MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry4
