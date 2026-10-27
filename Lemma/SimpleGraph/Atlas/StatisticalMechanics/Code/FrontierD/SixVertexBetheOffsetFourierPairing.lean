import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetFourierPairing
open StatMech StatMech.FrontierD


/--
[intervalIntegral_offsetProfile_mul_logDerivativePartialSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFourierPairing.lean)
-/
@[path]
private lemma intervalIntegral_offsetProfile_mul_logDerivativePartialSum_eq
  {lam : Real}
  {N : Nat}
-- given
  (hlam : 0 < lam) :
-- imply
  (∫ alpha in -Real.pi..Real.pi, sixVertexOffsetRapidityProfile lam alpha * sixVertexOffsetLogDerivativePartialSum lam N alpha) = -∑ n ∈ range N, (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) * (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real) := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_offsetProfile_mul_logDerivativePartialSum hlam N

/--
[sixVertexOffsetLogBoundary_add_pairing_eq_fourierPartialSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFourierPairing.lean)
-/
@[path]
private lemma sixVertexOffsetLogBoundary_add_pairing_eq_fourierPartialSum_eq
  {lam : Real}
  {N : Nat}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexOffsetLogBoundaryPartialSum lam N + (∫ alpha in -Real.pi..Real.pi, sixVertexOffsetRapidityProfile lam alpha * sixVertexOffsetLogDerivativePartialSum lam N alpha) = sixVertexOffsetFourierPartialSum lam N := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetLogBoundary_add_pairing_eq_fourierPartialSum hlam N

/--
[tendsto_sixVertexOffsetLogBoundary_add_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFourierPairing.lean)
-/
@[path]
private lemma tendsto_sixVertexOffsetLogBoundary_add_pairing_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Tendsto (fun N => sixVertexOffsetLogBoundaryPartialSum lam N + ∫ alpha in -Real.pi..Real.pi, sixVertexOffsetRapidityProfile lam alpha * sixVertexOffsetLogDerivativePartialSum lam N alpha) atTop (nhds (sixVertexAntiferroelectricGapRate lam)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOffsetLogBoundary_add_pairing hlam


-- created on 2026-10-23
