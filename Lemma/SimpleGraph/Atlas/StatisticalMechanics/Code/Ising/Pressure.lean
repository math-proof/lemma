import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.Pressure.Part4
open Finset Filter Topology StatMech StatMech.Ising


/--
[Z_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma Z_pos_eq
  [Fintype Ω]
  [Nonempty Ω]
  {β : ℝ}
  {E : Ω → ℝ} :
-- imply
  0 < Z β E := by
-- proof
  apply StatMech.Ising.Z_pos β E

/--
[Z_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma Z_prod_eq
  [Fintype Ω₁]
  [Fintype Ω₂]
  {β : ℝ}
  {E₁ : Ω₁ → ℝ}
  {E₂ : Ω₂ → ℝ} :
-- imply
  Z β (fun p : Ω₁ × Ω₂ => E₁ p.1 + E₂ p.2) = Z β E₁ * Z β E₂ := by
-- proof
  apply StatMech.Ising.Z_prod β E₁ E₂

/--
[Zpow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma Zpow_eq_eq
  [Fintype Ω]
  {β : ℝ}
  {E : Ω → ℝ}
  {n : ℕ} :
-- imply
  Zpow β E n = (Z β E) ^ n := by
-- proof
  apply StatMech.Ising.Zpow_eq β E n

/--
[Zpow_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma Zpow_pos_eq
  [Fintype Ω]
  [Nonempty Ω]
  {β : ℝ}
  {E : Ω → ℝ}
  {n : ℕ} :
-- imply
  0 < Zpow β E n := by
-- proof
  apply StatMech.Ising.Zpow_pos β E n

/--
[logZSeq_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma logZSeq_eq_eq
  [Fintype Ω]
  [Nonempty Ω]
  {β : ℝ}
  {E : Ω → ℝ}
  {n : ℕ} :
-- imply
  logZSeq β E n = n * Real.log (Z β E) := by
-- proof
  apply StatMech.Ising.logZSeq_eq β E n

/--
[logZSeq_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma logZSeq_subadditive_eq
  [Fintype Ω]
  [Nonempty Ω]
  {β : ℝ}
  {E : Ω → ℝ} :
-- imply
  Subadditive (logZSeq β E) := by
-- proof
  apply StatMech.Ising.logZSeq_subadditive β E

/--
[logZSeq_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma logZSeq_bddBelow_eq
  [Fintype Ω]
  [Nonempty Ω]
  {β : ℝ}
  {E : Ω → ℝ} :
-- imply
  BddBelow (Set.range fun n => logZSeq β E n / n) := by
-- proof
  apply StatMech.Ising.logZSeq_bddBelow β E

/--
[pressure_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma pressure_exists_eq
  [Fintype Ω]
  [Nonempty Ω]
  {β : ℝ}
  {E : Ω → ℝ} :
-- imply
  Tendsto (fun n => logZSeq β E n / n) atTop (𝓝 (pressure β E)) := by
-- proof
  apply StatMech.Ising.pressure_exists β E

/--
[pressure_eq_logZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma pressure_eq_logZ_eq
  [Fintype Ω]
  [Nonempty Ω]
  {β : ℝ}
  {E : Ω → ℝ} :
-- imply
  pressure β E = Real.log (Z β E) := by
-- proof
  apply StatMech.Ising.pressure_eq_logZ β E

/--
[isingZ_eq_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma isingZ_eq_Z_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  isingZ G β h = Z β (hamiltonian G h) := by
-- proof
  apply StatMech.Ising.isingZ_eq_Z β h

/--
[ising_pressure_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma ising_pressure_exists_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  Tendsto (fun n => logZSeq β (hamiltonian G h) n / n) atTop (𝓝 (pressure β (hamiltonian G h))) := by
-- proof
  apply StatMech.Ising.ising_pressure_exists β h

/--
[ising_pressure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean)
-/
@[path]
private lemma ising_pressure_eq_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  pressure β (hamiltonian G h) = Real.log (isingZ G β h) := by
-- proof
  apply StatMech.Ising.ising_pressure_eq β h


-- created on 2026-10-23
