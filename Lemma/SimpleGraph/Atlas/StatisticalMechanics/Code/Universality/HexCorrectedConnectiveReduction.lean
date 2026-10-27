import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedConnectiveReduction
open StatMech StatMech.Universality


/--
[hexStandard_connective_constant_of_corrected_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedConnectiveReduction.lean)
-/
@[path]
private lemma hexStandard_connective_constant_of_corrected_data_eq
-- given
  (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
  (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
  (HC : ∀ T (hT : 1 ≤ T), HexCSHighestCut T hT)
  (hconv : ∀ x, 0 < x → x < hexChiE → Summable (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * x ^ n)) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (hexStandardSAWCount n) ^ ((n : ℝ)⁻¹)) atTop (nhds kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hexStandard_connective_constant_of_corrected_data hlocal hwindow HC hconv


-- created on 2026-10-23
