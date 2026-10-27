import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Exact3D.ToyRG.Part4
open StatMech StatMech.Exact3D


/--
[toyCertificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ToyRG.lean)
-/
@[path]
private lemma toyCertificate_predictedExponent_eq_eq
  {scale : BlockScale}
  {thermalEigenvalue : ℝ}
-- given
  (hthermal : 1 < thermalEigenvalue) :
-- imply
  (toyCertificate scale hthermal).predictedExponent = Real.log scale.toReal / Real.log thermalEigenvalue := by
-- proof
  apply StatMech.Exact3D.toyCertificate_predictedExponent_eq scale hthermal


-- created on 2026-10-23
