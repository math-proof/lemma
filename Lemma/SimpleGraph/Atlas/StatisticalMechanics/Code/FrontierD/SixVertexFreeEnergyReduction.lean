import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexAntiferroelectricTransferConclusion_iff_bethePerron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergyReduction.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricTransferConclusion_iff_bethePerron_eq
  {c lam : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  SixVertexAntiferroelectricTransferConclusion c lam ↔ SixVertexBethePerronAsymptotics c lam := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricTransferConclusion_iff_bethePerron hc

/--
[sixVertexAntiferroelectricTransferConclusion_iff_canonicalBethePerron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergyReduction.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricTransferConclusion_iff_canonicalBethePerron_eq
  {c : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexAntiferroelectricTransferConclusion c (sixVertexAntiferroelectricLambda c) ↔ SixVertexBethePerronAsymptotics c (sixVertexAntiferroelectricLambda c) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricTransferConclusion_iff_canonicalBethePerron hc

/--
[sixVertexAntiferroelectricTransferConclusion_of_canonicalBethePerron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergyReduction.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricTransferConclusion_of_canonicalBethePerron_eq
  {c lam : ℝ}
-- given
  (hc : 2 < c)
  (hlam : 0 < lam)
  (hcosh : Real.cosh lam = (c ^ 2 - 2) / 2)
  (hbethe : SixVertexBethePerronAsymptotics c (sixVertexAntiferroelectricLambda c)) :
-- imply
  SixVertexAntiferroelectricTransferConclusion c lam := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricTransferConclusion_of_canonicalBethePerron hc hlam hcosh hbethe


-- created on 2026-10-23
