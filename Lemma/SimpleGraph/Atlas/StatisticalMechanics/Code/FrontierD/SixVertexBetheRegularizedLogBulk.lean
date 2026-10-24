import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogBulk
open StatMech StatMech.FrontierD


/--
[eventually_full_regularizedLogDisplacement_eq_two_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogBulk.lean)
-/
@[path]
private lemma eventually_full_regularizedLogDisplacement_eq_two_positive_eq
  {c : Real}
  {epsilon : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, (∑ i, (sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) - sixVertexRegularizedBetheLogKernel c epsilon (sixVertexCanonicalEvenAlignedHalfRoots hc s k i))) = 2 * sixVertexCanonicalEvenRegularizedBulkLogDisplacement hc epsilon s k := by
-- proof
  apply StatMech.FrontierD.eventually_full_regularizedLogDisplacement_eq_two_positive hc epsilon s

/--
[tendsto_sixVertexCanonicalEvenRegularizedFullLinearTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogBulk.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenRegularizedFullLinearTerm_eq
  {c epsilon : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (sixVertexCanonicalEvenRegularizedFullLinearTerm hc epsilon s) atTop (nhds ((2 * s : Real) * (∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenRegularizedFullLinearTerm hc hepsilon s

/--
[tendsto_sixVertexCanonicalEvenRegularizedFullTaylorRemainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogBulk.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenRegularizedFullTaylorRemainder_eq
  {c epsilon : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (fun k => sixVertexCanonicalEvenRegularizedFullLogDisplacement hc epsilon s k - sixVertexCanonicalEvenRegularizedFullLinearTerm hc epsilon s k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenRegularizedFullTaylorRemainder hc hepsilon s

/--
[tendsto_sixVertexCanonicalEvenRegularizedBulkLogDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogBulk.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenRegularizedBulkLogDisplacement_eq
  {c epsilon : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Tendsto (sixVertexCanonicalEvenRegularizedBulkLogDisplacement hc epsilon s) atTop (nhds ((2 * s : Real) / 2 * (∫ x in -Real.pi..Real.pi, sixVertexRegularizedBetheLogNormDerivative c epsilon x * sixVertexContinuousOffsetFourier c hc x))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenRegularizedBulkLogDisplacement hc hepsilon s


-- created on 2026-10-23
