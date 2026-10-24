import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.NontrivialAssembly
open StatMech StatMech.Sharpness


/--
[theta_ge_betaForm_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/NontrivialAssembly.lean)
-/
@[path]
private lemma theta_ge_betaForm_of_two_le_eq
  {d : ℕ}
  {J beta : ℝ}
-- given
  (hd : 2 ≤ d)
  (hJ : 0 < J)
  (hbeta : betaTildeC d J < beta) :
-- imply
  theta d (pBeta J beta).toNNReal (pBeta_toNNReal_le_one J beta) ≥ (beta - betaTildeC d J) / beta := by
-- proof
  apply StatMech.Sharpness.theta_ge_betaForm_of_two_le hd hJ hbeta

/--
[theta_ge_betaForm_of_two_le_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/NontrivialAssembly.lean)
-/
@[path]
private lemma theta_ge_betaForm_of_two_le_closed_eq
  {d : ℕ}
  {J beta : ℝ}
-- given
  (hd : 2 ≤ d)
  (hJ : 0 < J)
  (hbeta : betaTildeC d J ≤ beta) :
-- imply
  theta d (pBeta J beta).toNNReal (pBeta_toNNReal_le_one J beta) ≥ (beta - betaTildeC d J) / beta := by
-- proof
  apply StatMech.Sharpness.theta_ge_betaForm_of_two_le_closed hd hJ hbeta

/--
[sharpness_betaForm_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/NontrivialAssembly.lean)
-/
@[path]
private lemma sharpness_betaForm_of_two_le_eq
  {d : ℕ}
  {J : ℝ}
-- given
  (hd : 2 ≤ d)
  (hJ : 0 < J) :
-- imply
  tildePc d = pc d ∧ (∀ beta : ℝ, betaTildeC d J < beta ↔ (tildePc d : ℝ) < pBeta J beta) ∧ (∀ beta : ℝ, (pBeta J beta).toNNReal ∈ tildePcSet d → ∃ c > 0, ∃ C > 0, ∀ n, crossProb d (pBeta J beta).toNNReal (pBeta_toNNReal_le_one J beta) n ≤ C * Real.exp (-c * n)) ∧ (∀ beta : ℝ, betaTildeC d J < beta → theta d (pBeta J beta).toNNReal (pBeta_toNNReal_le_one J beta) ≥ (beta - betaTildeC d J) / beta) := by
-- proof
  apply StatMech.Sharpness.sharpness_betaForm_of_two_le hd hJ


-- created on 2026-10-23
