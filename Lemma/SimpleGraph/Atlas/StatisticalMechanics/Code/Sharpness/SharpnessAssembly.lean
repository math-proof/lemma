import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.SharpnessAssembly
open MeasureTheory Set Filter Topology Real StatMech StatMech.Sharpness


/--
[sas_betaTildeC_lt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessAssembly.lean)
-/
@[path]
private lemma sas_betaTildeC_lt_iff_eq
  {d : ℕ}
  {J β : ℝ}
-- given
  (hJ : 0 < J)
  (hd : 0 < d)
  (hpc : pc d < 1) :
-- imply
  betaTildeC d J < β ↔ (tildePc d : ℝ) < pBeta J β := by
-- proof
  apply StatMech.Sharpness.sas_betaTildeC_lt_iff hJ hd hpc

/--
[sas_lt_betaTildeC_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessAssembly.lean)
-/
@[path]
private lemma sas_lt_betaTildeC_iff_eq
  {d : ℕ}
  {J β : ℝ}
-- given
  (hJ : 0 < J)
  (hd : 0 < d)
  (hpc : pc d < 1) :
-- imply
  β < betaTildeC d J ↔ pBeta J β < (tildePc d : ℝ) := by
-- proof
  apply StatMech.Sharpness.sas_lt_betaTildeC_iff hJ hd hpc

/--
[sas_sharpness_betaForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessAssembly.lean)
-/
@[path]
private lemma sas_sharpness_betaForm_eq
  {d : ℕ}
  {J : ℝ}
-- given
  (hJ : 0 < J)
  (hd : 0 < d)
  (hpc : pc d < 1) :
-- imply
  tildePc d = pc d ∧ (∀ β : ℝ, (betaTildeC d J < β ↔ (tildePc d : ℝ) < pBeta J β)) ∧ (∀ β : ℝ, (pBeta J β).toNNReal ∈ tildePcSet d → ∃ c > 0, ∃ C > 0, ∀ n, crossProb d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) n ≤ C * Real.exp (-c * n)) ∧ (∀ β : ℝ, betaTildeC d J < β → theta d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) ≥ (β - betaTildeC d J) / β) := by
-- proof
  apply StatMech.Sharpness.sas_sharpness_betaForm hJ hd hpc


-- created on 2026-10-23
