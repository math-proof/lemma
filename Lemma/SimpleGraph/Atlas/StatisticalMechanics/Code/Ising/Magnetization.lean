import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
open MeasureTheory StatMech StatMech.Ising


/--
[measurable_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Magnetization.lean)
-/
@[path]
private lemma measurable_spin_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  Measurable (fun ω : ConfigSpace (Site d) => spin ω x) := by
-- proof
  apply StatMech.Ising.measurable_spin x

/--
[integrable_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Magnetization.lean)
-/
@[path]
private lemma integrable_spin_eq
  {d : ℕ}
  {x : Site d}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ] :
-- imply
  Integrable (fun ω : ConfigSpace (Site d) => spin ω x) μ := by
-- proof
  apply StatMech.Ising.integrable_spin x μ

/--
[abs_magnetization_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Magnetization.lean)
-/
@[path]
private lemma abs_magnetization_le_one_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  |magnetization d β| ≤ 1 := by
-- proof
  apply StatMech.Ising.abs_magnetization_le_one d β

/--
[magnetization_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Magnetization.lean)
-/
@[path]
private lemma magnetization_le_one_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  magnetization d β ≤ 1 := by
-- proof
  apply StatMech.Ising.magnetization_le_one d β

/--
[neg_one_le_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Magnetization.lean)
-/
@[path]
private lemma neg_one_le_magnetization_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  -1 ≤ magnetization d β := by
-- proof
  apply StatMech.Ising.neg_one_le_magnetization d β

/--
[mem_positiveMagnetizationSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Magnetization.lean)
-/
@[path]
private lemma mem_positiveMagnetizationSet_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  β ∈ positiveMagnetizationSet d ↔ 0 ≤ β ∧ 0 < magnetization d β := by
-- proof
  apply StatMech.Ising.mem_positiveMagnetizationSet


-- created on 2026-10-23
