import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.Onsanger
open StatMech StatMech.Onsager


/--
[main_high_temperature_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_high_temperature_expansion_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ} :
-- imply
  ons_Z G beta = (2 : ℝ) ^ Fintype.card V * (Real.cosh beta) ^ G.edgeFinset.card * ons_X G (Real.tanh beta) := by
-- proof
  apply StatMech.Onsager.main_high_temperature_expansion G beta

/--
[main_finite_pressure_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_finite_pressure_decomposition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hV : 0 < Fintype.card V) :
-- imply
  ons_pressureFinite G beta = Real.log 2 + (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) * Real.log (Real.cosh beta) + Real.log (ons_X G (Real.tanh beta)) / (Fintype.card V : ℝ) := by
-- proof
  apply StatMech.Onsager.main_finite_pressure_decomposition G beta hbeta hV

/--
[main_critical_beta_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_critical_beta_value_eq :
-- imply
  Real.sinh (2 * ons_betaC) = 1 := by
-- proof
  apply StatMech.Onsager.main_critical_beta_value

/--
[main_critical_beta_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_critical_beta_unique_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  Real.sinh (2 * beta) = 1 ↔ beta = ons_betaC := by
-- proof
  apply StatMech.Onsager.main_critical_beta_unique beta hbeta

/--
[main_pressure_continuous_at_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_pressure_continuous_at_critical_eq :
-- imply
  ContinuousAt ons_pressure ons_betaC := by
-- proof
  apply StatMech.Onsager.main_pressure_continuous_at_critical

/--
[main_torus_pressure_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_torus_pressure_decomposition_eq
  {L : ℕ}
  [Fact (2 < L)]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  ons_pressureFinite (onsTorusGraph L) beta = Real.log 2 + 2 * Real.log (Real.cosh beta) + Real.log (ons_X (onsTorusGraph L) (Real.tanh beta)) / ((L : ℝ) ^ 2) := by
-- proof
  apply StatMech.Onsager.main_torus_pressure_decomposition L beta hbeta

/--
[main_free_energy_from_spin_kacWard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_free_energy_from_spin_kacWard_eq
  {beta : ℝ}
-- given
  (hall : ∀ beta : ℝ, ons_spinKacWardIdentities beta)
  (hbeta : 0 ≤ beta) :
-- imply
  Filter.Tendsto (ons_torusPressureSeq beta) Filter.atTop (nhds (ons_pressure beta)) := by
-- proof
  apply StatMech.Onsager.main_free_energy_from_spin_kacWard hall beta hbeta

/--
[main_spin_kacWard_from_weighted_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_spin_kacWard_from_weighted_root_eq
  {beta : ℝ}
-- given
  (hweighted : ∀ (L : ℕ) (hL : 2 < L), letI : Fact (2 < L) := ⟨hL⟩ ons_weightedRootIdentity L) :
-- imply
  ons_spinKacWardIdentities beta := by
-- proof
  apply StatMech.Onsager.main_spin_kacWard_from_weighted_root hweighted beta

/--
[main_weighted_root_from_decorated_formal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_weighted_root_from_decorated_formal_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hformal : ons_decoratedFormalKacWardIdentity L) :
-- imply
  ons_weightedRootIdentity L := by
-- proof
  apply StatMech.Onsager.main_weighted_root_from_decorated_formal L hformal

/--
[main_spin_kacWard_from_decorated_formal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_spin_kacWard_from_decorated_formal_eq
  {beta : ℝ}
-- given
  (hformal : ∀ (L : ℕ) (hL : 2 < L), letI : Fact (2 < L) := ⟨hL⟩ ons_decoratedFormalKacWardIdentity L) :
-- imply
  ons_spinKacWardIdentities beta := by
-- proof
  apply StatMech.Onsager.main_spin_kacWard_from_decorated_formal hformal beta

/--
[main_free_energy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Onsanger.lean)
-/
@[path]
private lemma main_free_energy_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Filter.Tendsto (ons_torusPressureSeq beta) Filter.atTop (nhds (Real.log 2 + (1 / (8 * Real.pi ^ 2)) * ∫ k₁ in (-Real.pi)..Real.pi, ∫ k₂ in (-Real.pi)..Real.pi, Real.log (Real.cosh (2 * beta) ^ 2 - Real.sinh (2 * beta) * (Real.cos k₁ + Real.cos k₂)))) := by
-- proof
  apply StatMech.Onsager.main_free_energy beta hbeta


-- created on 2026-10-23
