import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronBounds
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexHalfFilledBetheCandidate_le_perron_of_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronBounds.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheCandidate_le_perron_of_nonzero_eq
  {c : Real}
  {k : Nat}
  {a : Complex}
-- given
  (hc : 2 < c)
  (hne : sixVertexHalfFilledBetheRotatedRealWave hc k a ≠ 0) :
-- imply
  sixVertexSymmetricBetheEigenvalueValue c (sixVertexPositiveHalfBetheRoots hc k) ≤ sixVertexLambdaAlongFour c 0 k := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheCandidate_le_perron_of_nonzero hc k a hne

/--
[sixVertexHalfFilledBetheCandidate_le_perron_width_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronBounds.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheCandidate_le_perron_width_four_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexSymmetricBetheEigenvalueValue c (sixVertexPositiveHalfBetheRoots hc 0) ≤ sixVertexLambdaAlongFour c 0 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheCandidate_le_perron_width_four hc


-- created on 2026-10-23
