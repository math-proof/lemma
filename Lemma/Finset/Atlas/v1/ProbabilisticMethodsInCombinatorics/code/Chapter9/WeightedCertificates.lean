import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
open MeasureTheory Real Finset TalagrandWeightedCertificates


namespace TalagrandWeightedCertificates

/--
[median_argument](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/WeightedCertificates.lean)
-/
@[path]
lemma median_argument
  {n : ℕ}
  {Ω : Fin n → Type*}
  {prob_le_m prob_ge_mt prob_le_mt prob_ge_m : ℝ}
  {K t : ℝ}
-- given
  (hprod1 : prob_le_m * prob_ge_mt ≤ Real.exp (-(t ^ 2) / K ^ 2))
  (hprod2 : prob_le_mt * prob_ge_m ≤ Real.exp (-(t ^ 2) / K ^ 2))
  (hmed_le : prob_le_m ≥ 1 / 2)
  (hmed_ge : prob_ge_m ≥ 1 / 2) :
-- imply
  prob_ge_mt + prob_le_mt ≤ 4 * Real.exp (-(t ^ 2) / K ^ 2) := by
-- proof
  have hexp_pos := Real.exp_pos (-(t ^ 2) / K ^ 2)
  have h2 : prob_ge_mt ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) := by nlinarith
  have h4 : prob_le_mt ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) := by nlinarith
  linarith
/-- Theorem 9.5.14 (Talagrand's inequality with weighted certificates): if $f$ has
weighted certificates with constant $K$ and $m$ is a median of $f$, then
$\mu(\{x : |f(x) - m| \geq t\}) \leq 4 e^{-t^2 / K^2}$. -/

end TalagrandWeightedCertificates


-- created on 2026-10-23
