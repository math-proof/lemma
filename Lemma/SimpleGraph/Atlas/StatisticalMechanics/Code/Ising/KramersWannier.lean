import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.KramersWannier.Part2
open Real StatMech StatMech.Ising


/--
[sinh_two_dualTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma sinh_two_dualTemp_eq
  {β : ℝ} :
-- imply
  Real.sinh (2 * dualTemp β) = 1 / Real.sinh (2 * β) := by
-- proof
  apply StatMech.Ising.sinh_two_dualTemp β

/--
[kramersWannier_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma kramersWannier_duality_eq
  {β : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  Real.sinh (2 * β) * Real.sinh (2 * dualTemp β) = 1 := by
-- proof
  apply StatMech.Ising.kramersWannier_duality β hβ

/--
[dualTemp_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma dualTemp_pos_eq
  {β : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  0 < dualTemp β := by
-- proof
  apply StatMech.Ising.dualTemp_pos β hβ

/--
[dualTemp_involution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma dualTemp_involution_eq
  {β : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  dualTemp (dualTemp β) = β := by
-- proof
  apply StatMech.Ising.dualTemp_involution β hβ

/--
[dualTemp_fixed_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma dualTemp_fixed_iff_eq
  {β : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  dualTemp β = β ↔ Real.sinh (2 * β) = 1 := by
-- proof
  apply StatMech.Ising.dualTemp_fixed_iff β hβ

/--
[selfDualPoint_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma selfDualPoint_pos_eq :
-- imply
  0 < selfDualPoint := by
-- proof
  apply StatMech.Ising.selfDualPoint_pos

/--
[sinh_two_selfDualPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma sinh_two_selfDualPoint_eq :
-- imply
  Real.sinh (2 * selfDualPoint) = 1 := by
-- proof
  apply StatMech.Ising.sinh_two_selfDualPoint

/--
[dualTemp_selfDualPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma dualTemp_selfDualPoint_eq :
-- imply
  dualTemp selfDualPoint = selfDualPoint := by
-- proof
  apply StatMech.Ising.dualTemp_selfDualPoint

/--
[selfDualPoint_eq_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma selfDualPoint_eq_log_eq :
-- imply
  selfDualPoint = (1 / 2) * Real.log (1 + Real.sqrt 2) := by
-- proof
  apply StatMech.Ising.selfDualPoint_eq_log

/--
[exists_unique_selfDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma exists_unique_selfDual_eq :
-- imply
  ∃! β : ℝ, 0 < β ∧ Real.sinh (2 * β) = 1 := by
-- proof
  apply StatMech.Ising.exists_unique_selfDual

/--
[kramersWannier_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma kramersWannier_critical_eq
  {βc : ℝ}
-- given
  (hβc : 0 < βc)
  (hfix : dualTemp βc = βc) :
-- imply
  Real.sinh (2 * βc) = 1 := by
-- proof
  apply StatMech.Ising.kramersWannier_critical βc hβc hfix

/--
[kramersWannier_critical_eq_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannier.lean)
-/
@[path]
private lemma kramersWannier_critical_eq_log_eq
  {βc : ℝ}
-- given
  (hβc : 0 < βc)
  (hfix : dualTemp βc = βc) :
-- imply
  βc = (1 / 2) * Real.log (1 + Real.sqrt 2) := by
-- proof
  apply StatMech.Ising.kramersWannier_critical_eq_log βc hβc hfix


-- created on 2026-10-23
