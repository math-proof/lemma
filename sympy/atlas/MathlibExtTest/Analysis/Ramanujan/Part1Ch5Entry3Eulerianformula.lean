/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch5Entry3Eulerianformula.lean -/


import sympy.atlas.Analysis.Ramanujan.Part1Ch5Entry3Eulerianformula
import Lemma.Real.Ramanujan.Part1Ch5Entry3Eulerianformula

/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 3 (Eulerian formula) API checks

Both power-series term definitions at zero and small indices, the Eulerian
evaluations at `-1` and `1`, and direct uses of the Entry 8 theorem and the
Entry 3 compatibility alias.
-/

namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry3Eulerianformula

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry4
open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry8Eulerianformula
open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry3Eulerianformula

-- Both series start at `1 / 2`.
example (z : ℂ) : chapter5Entry8BernoulliTerm z 0 = 1 / 2 := by
  simp [chapter5Entry8BernoulliTerm, bernoulli_one]
  norm_num

example (z : ℂ) : chapter5Entry8PsiTerm z 0 = 1 / 2 := by
  simp [chapter5Entry8PsiTerm, chapter5Psi]

-- At index `1` both series agree on `-z / 4`.
example (z : ℂ) : chapter5Entry8BernoulliTerm z 1 = -z / 4 := by
  simp [chapter5Entry8BernoulliTerm, bernoulli_two]
  ring

example (z : ℂ) : chapter5Entry8PsiTerm z 1 = -z / 4 := by
  have hPsi1 : chapter5Psi 1 (1 : ℂ) = 1 := by
    simp [chapter5Psi, eulerianNumber]
  simp [chapter5Entry8PsiTerm, hPsi1]
  ring

-- At index `2` both series vanish (`bernoulli 3 = 0`).
example (z : ℂ) : chapter5Entry8BernoulliTerm z 2 = 0 := by
  have hB3 : bernoulli 3 = 0 :=
    bernoulli_eq_zero_of_odd (by decide) (by norm_num)
  simp [chapter5Entry8BernoulliTerm, hB3]

example (z : ℂ) : chapter5Entry8PsiTerm z 2 = 0 := by
  have hPsi2 : chapter5Psi 2 (1 : ℂ) = 0 := by
    simp [chapter5Psi, Finset.sum_range_succ, eulerianNumber]
  simp [chapter5Entry8PsiTerm, hPsi2]

-- The `n = 0` Eulerian evaluation at `-1` is available through the component API.
example : chapter5Psi 0 (-1 : ℂ) = 1 := by
  have h := chapter5Entry8_psi_neg_one 0
  simpa using h

example : chapter5Psi 2 (-1 : ℂ) = 2 := by
  have h := chapter5Entry8_psi_neg_one 2
  simpa using h

-- Direct uses of the Entry 8 theorem.
example (z : ℂ) (hz : ‖z‖ < Real.pi) : Complex.exp z + 1 ≠ 0 :=
  (ramanujan_part1_ch5_entry8_eulerianformula 1 z le_rfl hz).1

example (z : ℂ) (hz : ‖z‖ < Real.pi) :
    HasSum (chapter5Entry8BernoulliTerm z) (1 / (Complex.exp z + 1)) :=
  (ramanujan_part1_ch5_entry8_eulerianformula 1 z le_rfl hz).2.2.2.1

-- Direct uses of the Entry 3 compatibility alias.
example (z : ℂ) (hz : ‖z‖ < Real.pi) : Complex.exp z + 1 ≠ 0 :=
  (ramanujan_part1_ch5_entry3_eulerianformula 1 z le_rfl hz).1

example (z : ℂ) (hz : ‖z‖ < Real.pi) :
    HasSum (chapter5Entry8PsiTerm z) (1 / (Complex.exp z + 1)) :=
  (ramanujan_part1_ch5_entry3_eulerianformula 2 z (by norm_num) hz).2.2.2.2

-- The standalone series components need no unrelated `n`.
example (z : ℂ) (hz : ‖z‖ < Real.pi) :
    HasSum (chapter5Entry8BernoulliTerm z) (1 / (Complex.exp z + 1)) :=
  chapter5Entry8_hasSum_bernoulli z hz

example (z : ℂ) (hz : ‖z‖ < Real.pi) :
    HasSum (chapter5Entry8PsiTerm z) (1 / (Complex.exp z + 1)) :=
  chapter5Entry8_hasSum_psi z hz

end MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry3Eulerianformula
