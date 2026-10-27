import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.Item3PercoLattice
open MeasureTheory StatMech StatMech.Sharpness


/--
[subcritical_decay_of_lt_tildeBetaCPerco](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Item3PercoLattice.lean)
-/
@[path]
private lemma subcritical_decay_of_lt_tildeBetaCPerco_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : beta < tildeBetaCPerco d) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n, crossProb d (bondParam beta) (bondParam_le_one beta) n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Sharpness.subcritical_decay_of_lt_tildeBetaCPerco hbeta


-- created on 2026-10-23
