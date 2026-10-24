import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary
open Finset StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexRectangleArrows


/--
[localWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma localWeight_nonneg_eq
  {N M : ℕ}
  {c : ℝ}
  {ω : SixVertexRectangleArrows N M}
  {v : Fin N × Fin M}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 ≤ ω.localWeight c v := by
-- proof
  apply StatMech.FrontierD.SixVertexRectangleArrows.localWeight_nonneg hc ω v

/--
[weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma weight_nonneg_eq
  {N M : ℕ}
  {c : ℝ}
  {ω : SixVertexRectangleArrows N M}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 ≤ ω.weight c := by
-- proof
  apply StatMech.FrontierD.SixVertexRectangleArrows.weight_nonneg hc ω

/--
[sixVertexRectangleBoundaryPartitionSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma sixVertexRectangleBoundaryPartitionSum_nonneg_eq
  {N M : ℕ}
  {c : ℝ}
  {ξ : SixVertexRectangleBoundary N M}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 ≤ sixVertexRectangleBoundaryPartitionSum N M c ξ := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBoundaryPartitionSum_nonneg N M hc ξ

/--
[sixVertexRectangleToroidalPartitionSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma sixVertexRectangleToroidalPartitionSum_nonneg_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 ≤ sixVertexRectangleToroidalPartitionSum N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleToroidalPartitionSum_nonneg N M hc

/--
[sixVertexRectangleBalancedPartitionSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_nonneg_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 ≤ sixVertexRectangleBalancedPartitionSum N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_nonneg N M hc

/--
[sixVertexRectangleFreePartitionSum_eq_sum_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma sixVertexRectangleFreePartitionSum_eq_sum_boundary_eq
  {N M : ℕ}
  {c : ℝ} :
-- imply
  sixVertexRectangleFreePartitionSum N M c = ∑ ξ : SixVertexRectangleBoundary N M, sixVertexRectangleBoundaryPartitionSum N M c ξ := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleFreePartitionSum_eq_sum_boundary N M c

/--
[sixVertexRectangleBalancedPartitionSum_le_toroidal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_le_toroidal_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c) :
-- imply
  sixVertexRectangleBalancedPartitionSum N M c ≤ sixVertexRectangleToroidalPartitionSum N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_le_toroidal N M hc

/--
[sixVertexRectangleBoundaryPartitionSum_le_maxToroidal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma sixVertexRectangleBoundaryPartitionSum_le_maxToroidal_eq
  {N M : ℕ}
  {c : ℝ}
  {ξ : SixVertexToroidalBoundary N M} :
-- imply
  sixVertexRectangleBoundaryPartitionSum N M c (sixVertexToroidalRectangleBoundary ξ) ≤ sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBoundaryPartitionSum_le_maxToroidal N M c ξ

/--
[sixVertexToroidalBoundary_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma sixVertexToroidalBoundary_card_eq
  {N M : ℕ} :
-- imply
  Fintype.card (SixVertexToroidalBoundary N M) = 2 ^ (N + M) := by
-- proof
  apply StatMech.FrontierD.sixVertexToroidalBoundary_card N M

/--
[sixVertexRectangleToroidalPartitionSum_le_card_mul_maxBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma sixVertexRectangleToroidalPartitionSum_le_card_mul_maxBoundary_eq
  {N M : ℕ}
  {c : ℝ} :
-- imply
  sixVertexRectangleToroidalPartitionSum N M c ≤ (2 : ℝ) ^ (N + M) * sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleToroidalPartitionSum_le_card_mul_maxBoundary N M c

/--
[sixVertexRectangleMaxToroidalBoundary_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean)
-/
@[path]
private lemma sixVertexRectangleMaxToroidalBoundary_exists_eq
  {N M : ℕ}
  {c : ℝ} :
-- imply
  ∃ ξ : SixVertexToroidalBoundary N M, sixVertexRectangleBoundaryPartitionSum N M c (sixVertexToroidalRectangleBoundary ξ) = sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleMaxToroidalBoundary_exists N M c


-- created on 2026-10-23
