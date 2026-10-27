import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectionSampling.Part2
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[boundaryTrace_abs_sub_le_of_lipschitzOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryProjectionSampling.lean)
-/
@[path]
private lemma boundaryTrace_abs_sub_le_of_lipschitzOn_eq
  {S : Set Complex}
  {L : NNReal}
  {sample boundaryPoint : Complex}
  {value mesh : Real}
-- given
  (Phi : Complex -> Complex)
  (hPhi : LipschitzOnWith L (fun z => (Phi z).im) S)
  (hsample : sample ∈ S)
  (hboundary : boundaryPoint ∈ S)
  (htrace : (Phi boundaryPoint).im = value)
  (hdist : dist sample boundaryPoint <= mesh) :
-- imply
  |value - (Phi sample).im| <= L * mesh := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.boundaryTrace_abs_sub_le_of_lipschitzOn Phi S L hPhi sample boundaryPoint value mesh hsample hboundary htrace hdist

/--
[PhysicalBoundaryProjectionSampling.vertexTrace_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryProjectionSampling.lean)
-/
@[path]
private lemma vertexTrace_abs_le_eq
  {N : Nat -> Nat}
  {mesh : Nat -> Real}
  {Phi : Complex -> Complex}
  {B : PhysicalBoundaryProjectionSampling N mesh Phi}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hx : fkIsingSquareFullVertexFixedBoundary (N k) x) :
-- imply
  |0 - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <= B.lipschitzConstant * mesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalBoundaryProjectionSampling.vertexTrace_abs_le B k x hx

/--
[PhysicalBoundaryProjectionSampling.faceTrace_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryProjectionSampling.lean)
-/
@[path]
private lemma faceTrace_abs_le_eq
  {N : Nat -> Nat}
  {mesh : Nat -> Real}
  {Phi : Complex -> Complex}
  {B : PhysicalBoundaryProjectionSampling N mesh Phi}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hc : fkIsingSquareFullFaceFixedBoundary (N k) c) :
-- imply
  |1 - (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <= B.lipschitzConstant * mesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalBoundaryProjectionSampling.faceTrace_abs_le B k c hc

/--
[PhysicalBoundaryProjectionSampling.traceRate_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryProjectionSampling.lean)
-/
@[path]
private lemma traceRate_tendsto_zero_eq
  {N : Nat -> Nat}
  {mesh : Nat -> Real}
  {Phi : Complex -> Complex}
  {B : PhysicalBoundaryProjectionSampling N mesh Phi}
-- given
  (hmesh : Tendsto mesh atTop (nhds 0)) :
-- imply
  Tendsto (fun k => (B.lipschitzConstant : Real) * mesh k) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalBoundaryProjectionSampling.traceRate_tendsto_zero B hmesh

/--
[PhysicalBoundaryProjectionSampling.vertexClamped_laplacian_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryProjectionSampling.lean)
-/
@[path]
private lemma vertexClamped_laplacian_le_eq
  {N : Nat -> Nat}
  {mesh : Nat -> Real}
  {Phi : Complex -> Complex}
  {B : PhysicalBoundaryProjectionSampling N mesh Phi}
  {k : Nat}
  {sampleBound : Real}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hx : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
  (hsample : |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y => (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x| <= sampleBound) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y => vertexBoundaryClampedSampledTarget (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi (some y)) x| <= sampleBound + 4 * (B.lipschitzConstant * mesh k) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalBoundaryProjectionSampling.vertexClamped_laplacian_le B hmesh_nonneg k sampleBound x hx hsample

/--
[PhysicalBoundaryProjectionSampling.faceClamped_laplacian_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryProjectionSampling.lean)
-/
@[path]
private lemma faceClamped_laplacian_le_eq
  {N : Nat -> Nat}
  {mesh : Nat -> Real}
  {Phi : Complex -> Complex}
  {B : PhysicalBoundaryProjectionSampling N mesh Phi}
  {k : Nat}
  {sampleBound : Real}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hc : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
  (hsample : |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d => (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c| <= sampleBound) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d => faceBoundaryClampedSampledTarget (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi (some d)) c| <= sampleBound + 4 * (B.lipschitzConstant * mesh k) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalBoundaryProjectionSampling.faceClamped_laplacian_le B hmesh_nonneg k sampleBound c hc hsample

/--
[PhysicalBoundaryProjectionSampling.vertexClamped_weightedLaplacian_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryProjectionSampling.lean)
-/
@[path]
private lemma vertexClamped_weightedLaplacian_le_eq
  {N : Nat -> Nat}
  {mesh : Nat -> Real}
  {Phi : Complex -> Complex}
  {B : PhysicalBoundaryProjectionSampling N mesh Phi}
  {k : Nat}
  {sampleBound : Real}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hx : Not (fkIsingSquareFullVertexFixedBoundary (N k) x))
  (hsample : |isingFiniteWeightedLaplacian (vertexGhostConductance (N k)) (vertexSampledImaginaryTarget (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi) (some x)| <= sampleBound) :
-- imply
  |isingFiniteWeightedLaplacian (vertexGhostConductance (N k)) (vertexBoundaryClampedSampledTarget (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi) (some x)| <= sampleBound + 4 * (B.lipschitzConstant * mesh k) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalBoundaryProjectionSampling.vertexClamped_weightedLaplacian_le B hmesh_nonneg k sampleBound x hx hsample

/--
[PhysicalBoundaryProjectionSampling.faceClamped_weightedLaplacian_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryProjectionSampling.lean)
-/
@[path]
private lemma faceClamped_weightedLaplacian_le_eq
  {N : Nat -> Nat}
  {mesh : Nat -> Real}
  {Phi : Complex -> Complex}
  {B : PhysicalBoundaryProjectionSampling N mesh Phi}
  {k : Nat}
  {sampleBound : Real}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hc : Not (fkIsingSquareFullFaceFixedBoundary (N k) c))
  (hsample : |isingFiniteWeightedLaplacian (faceGhostConductance (N k)) (faceSampledImaginaryTarget (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi) (some c)| <= sampleBound) :
-- imply
  |isingFiniteWeightedLaplacian (faceGhostConductance (N k)) (faceBoundaryClampedSampledTarget (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi) (some c)| <= sampleBound + 4 * (B.lipschitzConstant * mesh k) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalBoundaryProjectionSampling.faceClamped_weightedLaplacian_le B hmesh_nonneg k sampleBound c hc hsample


-- created on 2026-10-23
