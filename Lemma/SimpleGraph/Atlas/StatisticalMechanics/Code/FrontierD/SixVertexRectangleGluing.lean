import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing.Part6
open Finset StatMech StatMech.FrontierD


/--
[sixVertexRectangleGlueQuadrants_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleGlueQuadrants_boundary_eq
  {N M : ℕ}
  {lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M}
-- given
  (hN : 0 < N)
  (hM : 0 < M) :
-- imply
  sixVertexRectangleBoundary (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight) = sixVertexRectangleGlueBoundary (sixVertexRectangleBoundary lowerLeft) (sixVertexRectangleBoundary lowerRight) (sixVertexRectangleBoundary upperLeft) (sixVertexRectangleBoundary upperRight) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleGlueQuadrants_boundary hN hM lowerLeft lowerRight upperLeft upperRight

/--
[sixVertexRectangle_reflectedQuadrantsCompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangle_reflectedQuadrantsCompatible_eq
  {N M : ℕ}
  {ξ : SixVertexRectangleBoundary N M}
  {ω₀ ω₁ ω₂ ω₃ : SixVertexRectangleArrows N M}
-- given
  (h₀ : sixVertexRectangleBoundary ω₀ = ξ)
  (h₁ : sixVertexRectangleBoundary ω₁ = ξ)
  (h₂ : sixVertexRectangleBoundary ω₂ = ξ)
  (h₃ : sixVertexRectangleBoundary ω₃ = ξ) :
-- imply
  SixVertexRectangleQuadrantsCompatible ω₀ (sixVertexRectangleReflectHorizontal ω₁) (sixVertexRectangleReflectVertical ω₂) (sixVertexRectangleReflectHorizontal (sixVertexRectangleReflectVertical ω₃)) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangle_reflectedQuadrantsCompatible ξ ω₀ ω₁ ω₂ ω₃ h₀ h₁ h₂ h₃

/--
[sixVertexRectangle_reflectedGlueBoundary_eq_toroidal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangle_reflectedGlueBoundary_eq_toroidal_eq
  {N M : ℕ}
  {ξ : SixVertexToroidalBoundary N M} :
-- imply
  sixVertexRectangleGlueBoundary (sixVertexToroidalRectangleBoundary ξ) (sixVertexBoundaryReflectHorizontal (sixVertexToroidalRectangleBoundary ξ)) (sixVertexBoundaryReflectVertical (sixVertexToroidalRectangleBoundary ξ)) (sixVertexBoundaryReflectHorizontal (sixVertexBoundaryReflectVertical (sixVertexToroidalRectangleBoundary ξ))) = sixVertexToroidalRectangleBoundary (sixVertexDoubledToroidalBoundary ξ) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangle_reflectedGlueBoundary_eq_toroidal ξ

/--
[sixVertexRectangleGlueQuadrants_localWeight_lowerLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleGlueQuadrants_localWeight_lowerLeft_eq
  {N M : ℕ}
  {c : ℝ}
  {lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M}
  {i : Fin N}
  {j : Fin M}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hcompat : SixVertexRectangleQuadrantsCompatible lowerLeft lowerRight upperLeft upperRight) :
-- imply
  (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c (Fin.castAdd N i, Fin.castAdd M j) = lowerLeft.localWeight c (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleGlueQuadrants_localWeight_lowerLeft hN hM c lowerLeft lowerRight upperLeft upperRight hcompat i j

/--
[sixVertexRectangleGlueQuadrants_localWeight_lowerRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleGlueQuadrants_localWeight_lowerRight_eq
  {N M : ℕ}
  {c : ℝ}
  {lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M}
  {i : Fin N}
  {j : Fin M}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hcompat : SixVertexRectangleQuadrantsCompatible lowerLeft lowerRight upperLeft upperRight) :
-- imply
  (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c (Fin.natAdd N i, Fin.castAdd M j) = lowerRight.localWeight c (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleGlueQuadrants_localWeight_lowerRight hN hM c lowerLeft lowerRight upperLeft upperRight hcompat i j

/--
[sixVertexRectangleGlueQuadrants_localWeight_upperLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleGlueQuadrants_localWeight_upperLeft_eq
  {N M : ℕ}
  {c : ℝ}
  {lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M}
  {i : Fin N}
  {j : Fin M}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hcompat : SixVertexRectangleQuadrantsCompatible lowerLeft lowerRight upperLeft upperRight) :
-- imply
  (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c (Fin.castAdd N i, Fin.natAdd M j) = upperLeft.localWeight c (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleGlueQuadrants_localWeight_upperLeft hN hM c lowerLeft lowerRight upperLeft upperRight hcompat i j

/--
[sixVertexRectangleGlueQuadrants_localWeight_upperRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleGlueQuadrants_localWeight_upperRight_eq
  {N M : ℕ}
  {c : ℝ}
  {lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M}
  {i : Fin N}
  {j : Fin M}
-- given
  (hN : 0 < N)
  (hM : 0 < M) :
-- imply
  (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c (Fin.natAdd N i, Fin.natAdd M j) = upperRight.localWeight c (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleGlueQuadrants_localWeight_upperRight hN hM c lowerLeft lowerRight upperLeft upperRight i j

/--
[sixVertexRectangleGlueQuadrants_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleGlueQuadrants_weight_eq
  {N M : ℕ}
  {c : ℝ}
  {lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hcompat : SixVertexRectangleQuadrantsCompatible lowerLeft lowerRight upperLeft upperRight) :
-- imply
  (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).weight c = lowerLeft.weight c * lowerRight.weight c * upperLeft.weight c * upperRight.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleGlueQuadrants_weight hN hM c lowerLeft lowerRight upperLeft upperRight hcompat

/--
[sixVertexRectangleReflectedGlue_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleReflectedGlue_compatible_eq
  {N M : ℕ}
  {ξ : SixVertexRectangleBoundary N M}
  {omega : SixVertexRectangleFourBoundaryCopies ξ} :
-- imply
  SixVertexRectangleQuadrantsCompatible omega.1.1 (sixVertexRectangleReflectHorizontal omega.2.1.1) (sixVertexRectangleReflectVertical omega.2.2.1.1) (sixVertexRectangleReflectHorizontal (sixVertexRectangleReflectVertical omega.2.2.2.1)) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectedGlue_compatible omega

/--
[sixVertexRectangleReflectedGlue_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleReflectedGlue_boundary_eq
  {N M : ℕ}
  {ξ : SixVertexToroidalBoundary N M}
  {omega : SixVertexRectangleFourBoundaryCopies (sixVertexToroidalRectangleBoundary ξ)}
-- given
  (hN : 0 < N)
  (hM : 0 < M) :
-- imply
  sixVertexRectangleBoundary (sixVertexRectangleReflectedGlue omega) = sixVertexToroidalRectangleBoundary (sixVertexDoubledToroidalBoundary ξ) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectedGlue_boundary hN hM omega

/--
[sixVertexRectangleReflectedGlue_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleReflectedGlue_weight_eq
  {N M : ℕ}
  {c : ℝ}
  {ξ : SixVertexRectangleBoundary N M}
  {omega : SixVertexRectangleFourBoundaryCopies ξ}
-- given
  (hN : 0 < N)
  (hM : 0 < M) :
-- imply
  (sixVertexRectangleReflectedGlue omega).weight c = omega.1.1.weight c * omega.2.1.1.weight c * omega.2.2.1.1.weight c * omega.2.2.2.1.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectedGlue_weight hN hM c omega

/--
[sixVertexRectangleReflectedGlue_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleReflectedGlue_injective_eq
  {N M : ℕ}
  {ξ : SixVertexRectangleBoundary N M} :
-- imply
  Function.Injective (sixVertexRectangleReflectedGlue : SixVertexRectangleFourBoundaryCopies ξ → SixVertexRectangleArrows (N + N) (M + M)) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectedGlue_injective

/--
[sixVertexRectangleReflectedGlueBoundaryFiber_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleReflectedGlueBoundaryFiber_injective_eq
  {N M : ℕ}
  {ξ : SixVertexToroidalBoundary N M}
-- given
  (hN : 0 < N)
  (hM : 0 < M) :
-- imply
  Function.Injective (sixVertexRectangleReflectedGlueBoundaryFiber hN hM ξ) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectedGlueBoundaryFiber_injective hN hM ξ

/--
[sixVertexRectangleBoundaryPartitionSum_eq_fiberSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleBoundaryPartitionSum_eq_fiberSum_eq
  {N M : ℕ}
  {c : ℝ}
  {ξ : SixVertexRectangleBoundary N M} :
-- imply
  sixVertexRectangleBoundaryPartitionSum N M c ξ = ∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBoundaryPartitionSum_eq_fiberSum N M c ξ

/--
[sixVertexRectangleBoundaryPartitionSum_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleBoundaryPartitionSum_pow_four_eq
  {N M : ℕ}
  {c : ℝ}
  {ξ : SixVertexRectangleBoundary N M} :
-- imply
  sixVertexRectangleBoundaryPartitionSum N M c ξ ^ 4 = ∑ omega : SixVertexRectangleFourBoundaryCopies ξ, omega.1.1.weight c * omega.2.1.1.weight c * omega.2.2.1.1.weight c * omega.2.2.2.1.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBoundaryPartitionSum_pow_four N M c ξ

/--
[sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBoundary_eq
  {N M : ℕ}
  {c : ℝ}
  {ξ : SixVertexToroidalBoundary N M}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hc : 0 ≤ c) :
-- imply
  sixVertexRectangleBoundaryPartitionSum N M c (sixVertexToroidalRectangleBoundary ξ) ^ 4 ≤ sixVertexRectangleBoundaryPartitionSum (N + N) (M + M) c (sixVertexToroidalRectangleBoundary (sixVertexDoubledToroidalBoundary ξ)) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBoundary hN hM hc ξ

/--
[sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledToroidal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledToroidal_eq
  {N M : ℕ}
  {c : ℝ}
  {ξ : SixVertexToroidalBoundary N M}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hc : 0 ≤ c) :
-- imply
  sixVertexRectangleBoundaryPartitionSum N M c (sixVertexToroidalRectangleBoundary ξ) ^ 4 ≤ sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledToroidal hN hM hc ξ

/--
[sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean)
-/
@[path]
private lemma sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubled_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hc : 0 ≤ c) :
-- imply
  sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c ^ 4 ≤ sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubled hN hM hc


-- created on 2026-10-23
