import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CriticalTransfer.Part2
open StatMech StatMech.Onsager


/--
[ons_bond_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalTransfer.lean)
-/
@[path]
private lemma ons_bond_abs_le_one_eq
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  |bond s e| ≤ 1 := by
-- proof
  apply StatMech.Onsager.ons_bond_abs_le_one s e

/--
[ons_hamiltonian_zero_abs_le_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalTransfer.lean)
-/
@[path]
private lemma ons_hamiltonian_zero_abs_le_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V} :
-- imply
  |hamiltonian G 0 s| ≤ G.edgeFinset.card := by
-- proof
  apply StatMech.Onsager.ons_hamiltonian_zero_abs_le_edges G s

/--
[ons_Z_scaled_energy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalTransfer.lean)
-/
@[path]
private lemma ons_Z_scaled_energy_eq
  {beta : ℝ}
  [Fintype Omega]
  {E : Omega → ℝ} :
-- imply
  StatMech.Ising.Z 1 (fun s => beta * E s) = StatMech.Ising.Z beta E := by
-- proof
  apply StatMech.Onsager.ons_Z_scaled_energy beta E

/--
[ons_log_Z_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalTransfer.lean)
-/
@[path]
private lemma ons_log_Z_lipschitz_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta gamma : ℝ} :
-- imply
  |Real.log (ons_Z G beta) - Real.log (ons_Z G gamma)| ≤ |beta - gamma| * G.edgeFinset.card := by
-- proof
  apply StatMech.Onsager.ons_log_Z_lipschitz G beta gamma

/--
[ons_torusPressure_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalTransfer.lean)
-/
@[path]
private lemma ons_torusPressure_lipschitz_eq
  {L : ℕ}
  [Fact (2 < L)]
  {beta gamma : ℝ} :
-- imply
  |ons_pressureFinite (onsTorusGraph L) beta - ons_pressureFinite (onsTorusGraph L) gamma| ≤ 2 * |beta - gamma| := by
-- proof
  apply StatMech.Onsager.ons_torusPressure_lipschitz L beta gamma

/--
[ons_torusPressureSeq_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalTransfer.lean)
-/
@[path]
private lemma ons_torusPressureSeq_lipschitz_eq
  {beta gamma : ℝ}
  {L : ℕ} :
-- imply
  |ons_torusPressureSeq beta L - ons_torusPressureSeq gamma L| ≤ 2 * |beta - gamma| := by
-- proof
  apply StatMech.Onsager.ons_torusPressureSeq_lipschitz beta gamma L

/--
[ons_free_energy_critical_of_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalTransfer.lean)
-/
@[path]
private lemma ons_free_energy_critical_of_noncritical_eq
-- given
  (hcontinuous : ContinuousAt ons_pressure ons_betaC)
  (hnoncritical : ∀ beta : ℝ, 0 ≤ beta → beta ≠ ons_betaC → Filter.Tendsto (ons_torusPressureSeq beta) Filter.atTop (nhds (ons_pressure beta))) :
-- imply
  Filter.Tendsto (ons_torusPressureSeq ons_betaC) Filter.atTop (nhds (ons_pressure ons_betaC)) := by
-- proof
  apply StatMech.Onsager.ons_free_energy_critical_of_noncritical hcontinuous hnoncritical


-- created on 2026-10-23
