import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
open Finset StatMech StatMech.FrontierD


/--
[sixVertexDoubledToroidalBoundary_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedBoundaryGluing.lean)
-/
@[path]
private lemma sixVertexDoubledToroidalBoundary_balanced_eq
  {N M : ℕ}
  {xi : SixVertexToroidalBoundary N M} :
-- imply
  (sixVertexDoubledToroidalBoundary xi).Balanced := by
-- proof
  apply StatMech.FrontierD.sixVertexDoubledToroidalBoundary_balanced xi

/--
[sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBalanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedBoundaryGluing.lean)
-/
@[path]
private lemma sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBalanced_eq
  {N M : ℕ}
  {c : Real}
  {xi : SixVertexToroidalBoundary N M}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hc : 0 <= c) :
-- imply
  sixVertexRectangleBoundaryPartitionSum N M c (sixVertexToroidalRectangleBoundary xi) ^ 4 <= sixVertexRectangleBalancedPartitionSum (N + N) (M + M) c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBalanced hN hM hc xi

/--
[sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubledBalanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedBoundaryGluing.lean)
-/
@[path]
private lemma sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubledBalanced_eq
  {N M : ℕ}
  {c : Real}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hc : 0 <= c) :
-- imply
  sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c ^ 4 <= sixVertexRectangleBalancedPartitionSum (N + N) (M + M) c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubledBalanced hN hM hc

/--
[sixVertexTorusArrowPartition_boundaryControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedBoundaryGluing.lean)
-/
@[path]
private lemma sixVertexTorusArrowPartition_boundaryControl_eq
  {T : EvenTorus}
  {c : Real}
-- given
  (hc : 0 <= c) :
-- imply
  sixVertexTorusArrowPartitionSum T c <= (2 : Real) ^ (T.width + T.height) * sixVertexRectangleMaxToroidalBoundaryPartitionSum T.width T.height c ∧ sixVertexRectangleMaxToroidalBoundaryPartitionSum T.width T.height c ^ 4 <= sixVertexTorusArrowPartitionSum T.double c := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusArrowPartition_boundaryControl T hc

/--
[sixVertexTorusArrowPartitionSum_pow_four_le_boundaryFactor_mul_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedBoundaryGluing.lean)
-/
@[path]
private lemma sixVertexTorusArrowPartitionSum_pow_four_le_boundaryFactor_mul_balanced_eq
  {T : EvenTorus}
  {c : Real}
-- given
  (hc : 0 <= c) :
-- imply
  sixVertexTorusArrowPartitionSum T c ^ 4 <= (2 : Real) ^ (4 * (T.width + T.height)) * sixVertexRectangleBalancedPartitionSum (T.width + T.width) (T.height + T.height) c := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusArrowPartitionSum_pow_four_le_boundaryFactor_mul_balanced T hc

/--
[sixVertexTorusArrowPartition_balancedBoundaryControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedBoundaryGluing.lean)
-/
@[path]
private lemma sixVertexTorusArrowPartition_balancedBoundaryControl_eq
  {T : EvenTorus}
  {c : Real}
-- given
  (hc : 0 <= c) :
-- imply
  sixVertexRectangleBalancedPartitionSum (T.width + T.width) (T.height + T.height) c <= sixVertexTorusArrowPartitionSum T.double c ∧ sixVertexTorusArrowPartitionSum T c ^ 4 <= (2 : Real) ^ (4 * (T.width + T.height)) * sixVertexRectangleBalancedPartitionSum (T.width + T.width) (T.height + T.height) c := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusArrowPartition_balancedBoundaryControl T hc


-- created on 2026-10-23
