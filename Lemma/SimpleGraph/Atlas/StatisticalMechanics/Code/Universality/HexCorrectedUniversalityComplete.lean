import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedUniversalityComplete
open StatMech StatMech.Universality


/--
[hexStandard_connective_constant_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedUniversalityComplete.lean)
-/
@[path]
private lemma hexStandard_connective_constant_of_local_eq
-- given
  (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹)) atTop (nhds kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hexStandard_connective_constant_of_local hlocal

/--
[hexStandard_connective_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedUniversalityComplete.lean)
-/
@[path]
private lemma hexStandard_connective_constant_eq :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹)) atTop (nhds kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hexStandard_connective_constant

/--
[hexStandard_connective_constant_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedUniversalityComplete.lean)
-/
@[path]
private lemma hexStandard_connective_constant_tendsto_eq :
-- imply
  Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹)) atTop (nhds (Real.sqrt (2 + Real.sqrt 2))) := by
-- proof
  apply StatMech.Universality.hexStandard_connective_constant_tendsto


-- created on 2026-10-23
