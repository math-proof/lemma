import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFiniteWeightedBoundaryError_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma isingFiniteWeightedBoundaryError_le_eq
  [Fintype V]
  [Nonempty V]
  {data target : V → Real}
  {bound : Real}
-- given
  (boundary : V → Prop)
  (hbound : 0 ≤ bound)
  (hboundary : ∀ x, boundary x → |data x - target x| ≤ bound) :
-- imply
  isingFiniteWeightedBoundaryError boundary data target ≤ bound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFiniteWeightedBoundaryError_le boundary data target bound hbound hboundary

/--
[isingFiniteWeightedTargetResidual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma isingFiniteWeightedTargetResidual_le_eq
  [Fintype V]
  [Nonempty V]
  {conductance : V → V → Real}
  {target : V → Real}
  {bound : Real}
-- given
  (boundary : V → Prop)
  (hbound : 0 ≤ bound)
  (hresidual : ∀ x, ¬ boundary x → |isingFiniteWeightedLaplacian conductance target x| ≤ bound) :
-- imply
  isingFiniteWeightedTargetResidual conductance boundary target ≤ bound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFiniteWeightedTargetResidual_le conductance boundary target bound hbound hresidual

/--
[fullSquareScaledVertexEmbedding_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledVertexEmbedding_east_eq
  {n : Nat}
  {scale : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .east) :
-- imply
  fullSquareScaledVertexEmbedding n scale (fkIsingSquareNeighbor n x .east h) = fullSquareScaledVertexEmbedding n scale x + (scale : Complex) * (1 + Complex.I) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding_east n scale x h

/--
[fullSquareScaledVertexEmbedding_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledVertexEmbedding_north_eq
  {n : Nat}
  {scale : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .north) :
-- imply
  fullSquareScaledVertexEmbedding n scale (fkIsingSquareNeighbor n x .north h) = fullSquareScaledVertexEmbedding n scale x + (scale : Complex) * (1 - Complex.I) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding_north n scale x h

/--
[fullSquareScaledVertexEmbedding_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledVertexEmbedding_west_eq
  {n : Nat}
  {scale : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .west) :
-- imply
  fullSquareScaledVertexEmbedding n scale (fkIsingSquareNeighbor n x .west h) = fullSquareScaledVertexEmbedding n scale x - (scale : Complex) * (1 + Complex.I) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding_west n scale x h

/--
[fullSquareScaledVertexEmbedding_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledVertexEmbedding_south_eq
  {n : Nat}
  {scale : Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  fullSquareScaledVertexEmbedding n scale (fkIsingSquareNeighbor n x .south h) = fullSquareScaledVertexEmbedding n scale x - (scale : Complex) * (1 - Complex.I) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding_south n scale x h

/--
[fullSquareScaledFaceEmbedding_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledFaceEmbedding_east_eq
  {n : Nat}
  {scale : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (h : c.1.1 + 1 < 2 * n) :
-- imply
  fullSquareScaledFaceEmbedding n scale (faceEastNeighbor n c h) = fullSquareScaledFaceEmbedding n scale c + (scale : Complex) * (1 + Complex.I) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFaceEmbedding_east n scale c h

/--
[fullSquareScaledFaceEmbedding_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledFaceEmbedding_north_eq
  {n : Nat}
  {scale : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (h : c.2.1 + 1 < 2 * n) :
-- imply
  fullSquareScaledFaceEmbedding n scale (faceNorthNeighbor n c h) = fullSquareScaledFaceEmbedding n scale c + (scale : Complex) * (1 - Complex.I) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFaceEmbedding_north n scale c h

/--
[fullSquareScaledFaceEmbedding_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledFaceEmbedding_west_eq
  {n : Nat}
  {scale : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (h : 0 < c.1.1) :
-- imply
  fullSquareScaledFaceEmbedding n scale (faceWestNeighbor n c h) = fullSquareScaledFaceEmbedding n scale c - (scale : Complex) * (1 + Complex.I) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFaceEmbedding_west n scale c h

/--
[fullSquareScaledFaceEmbedding_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledFaceEmbedding_south_eq
  {n : Nat}
  {scale : Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (h : 0 < c.2.1) :
-- imply
  fullSquareScaledFaceEmbedding n scale (faceSouthNeighbor n c h) = fullSquareScaledFaceEmbedding n scale c - (scale : Complex) * (1 - Complex.I) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFaceEmbedding_south n scale c h

/--
[fullSquareScaledVertex_sampledLaplacian_eq_stencil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledVertex_sampledLaplacian_eq_stencil_eq
  {n : Nat}
  {scale : Real}
  {f : Complex → Real}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (heast : fkIsingSquareDirectionAvailable n x .east)
  (hnorth : fkIsingSquareDirectionAvailable n x .north)
  (hwest : fkIsingSquareDirectionAvailable n x .west)
  (hsouth : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y ↦ f (fullSquareScaledVertexEmbedding n scale y)) x = complexDirectionalFourNeighborStencil f (fullSquareScaledVertexEmbedding n scale x) (1 + Complex.I) (1 - Complex.I) scale := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertex_sampledLaplacian_eq_stencil n scale f x heast hnorth hwest hsouth

/--
[fullSquareScaledFace_sampledLaplacian_eq_stencil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledFace_sampledLaplacian_eq_stencil_eq
  {n : Nat}
  {scale : Real}
  {f : Complex → Real}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (heast : c.1.1 + 1 < 2 * n)
  (hnorth : c.2.1 + 1 < 2 * n)
  (hwest : 0 < c.1.1)
  (hsouth : 0 < c.2.1) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d ↦ f (fullSquareScaledFaceEmbedding n scale d)) c = complexDirectionalFourNeighborStencil f (fullSquareScaledFaceEmbedding n scale c) (1 + Complex.I) (1 - Complex.I) scale := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFace_sampledLaplacian_eq_stencil n scale f c heast hnorth hwest hsouth

/--
[fullSquareScaledVertex_sampledLaplacian_le_fourthOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledVertex_sampledLaplacian_le_fourthOrder_eq
  {n : Nat}
  {scale : Real}
  {f : Complex → Real}
  {x : FKIsingSquareFullVertexNode n}
  {M₁ M₂ : Real}
-- given
  (heast : fkIsingSquareDirectionAvailable n x .east)
  (hnorth : fkIsingSquareDirectionAvailable n x .north)
  (hwest : fkIsingSquareDirectionAvailable n x .west)
  (hsouth : fkIsingSquareDirectionAvailable n x .south)
  (hg₁ : ContDiff Real 4 (fun t : Real ↦ f (fullSquareScaledVertexEmbedding n scale x + (t : Complex) * (1 + Complex.I))))
  (hg₂ : ContDiff Real 4 (fun t : Real ↦ f (fullSquareScaledVertexEmbedding n scale x + (t : Complex) * (1 - Complex.I))))
  (hfourth₁ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f (fullSquareScaledVertexEmbedding n scale x + (s : Complex) * (1 + Complex.I))) t| ≤ M₁)
  (hfourth₂ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f (fullSquareScaledVertexEmbedding n scale x + (s : Complex) * (1 - Complex.I))) t| ≤ M₂)
  (hharmonic : iteratedDeriv 2 (fun t : Real ↦ f (fullSquareScaledVertexEmbedding n scale x + (t : Complex) * (1 + Complex.I))) 0 + iteratedDeriv 2 (fun t : Real ↦ f (fullSquareScaledVertexEmbedding n scale x + (t : Complex) * (1 - Complex.I))) 0 = 0) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y ↦ f (fullSquareScaledVertexEmbedding n scale y)) x| ≤ (M₁ + M₂) * |scale| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertex_sampledLaplacian_le_fourthOrder n scale f x heast hnorth hwest hsouth M₁ M₂ hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

/--
[fullSquareScaledFace_sampledLaplacian_le_fourthOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledFace_sampledLaplacian_le_fourthOrder_eq
  {n : Nat}
  {scale : Real}
  {f : Complex → Real}
  {c : FKIsingSquareFullFaceNode n}
  {M₁ M₂ : Real}
-- given
  (heast : c.1.1 + 1 < 2 * n)
  (hnorth : c.2.1 + 1 < 2 * n)
  (hwest : 0 < c.1.1)
  (hsouth : 0 < c.2.1)
  (hg₁ : ContDiff Real 4 (fun t : Real ↦ f (fullSquareScaledFaceEmbedding n scale c + (t : Complex) * (1 + Complex.I))))
  (hg₂ : ContDiff Real 4 (fun t : Real ↦ f (fullSquareScaledFaceEmbedding n scale c + (t : Complex) * (1 - Complex.I))))
  (hfourth₁ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f (fullSquareScaledFaceEmbedding n scale c + (s : Complex) * (1 + Complex.I))) t| ≤ M₁)
  (hfourth₂ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f (fullSquareScaledFaceEmbedding n scale c + (s : Complex) * (1 - Complex.I))) t| ≤ M₂)
  (hharmonic : iteratedDeriv 2 (fun t : Real ↦ f (fullSquareScaledFaceEmbedding n scale c + (t : Complex) * (1 + Complex.I))) 0 + iteratedDeriv 2 (fun t : Real ↦ f (fullSquareScaledFaceEmbedding n scale c + (t : Complex) * (1 - Complex.I))) 0 = 0) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d ↦ f (fullSquareScaledFaceEmbedding n scale d)) c| ≤ (M₁ + M₂) * |scale| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFace_sampledLaplacian_le_fourthOrder n scale f c heast hnorth hwest hsouth M₁ M₂ hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

/--
[fullSquareScaledCoordinateEmbedding_unitAxial_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledCoordinateEmbedding_unitAxial_dist_eq
  {scale : Real}
  {u v : Int × Int}
-- given
  (hscale : 0 ≤ scale)
  (hunit : v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1) ∨ v = (u.1 - 1, u.2) ∨ v = (u.1, u.2 - 1)) :
-- imply
  dist (fullSquareScaledCoordinateEmbedding scale v) (fullSquareScaledCoordinateEmbedding scale u) ≤ scale := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledCoordinateEmbedding_unitAxial_dist scale hscale u v hunit

/--
[FullSquareCoordinateEmbeddingCompatibility.incidenceDistance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma incidenceDistance_eq
  {N : Nat → Nat}
  {hN : ∀ k, 0 < N k}
  {vertexEmbedding : ∀ k, FKIsingSquareFullVertexNode (N k) → Complex}
  {faceEmbedding : ∀ k, FKIsingSquareFullFaceNode (N k) → Complex}
  {mesh : Nat → Real}
  {C : FullSquareCoordinateEmbeddingCompatibility N vertexEmbedding faceEmbedding mesh}
  {k : Nat}
  {e : FKIsingSquareInteriorRadialIncidence (N k) (hN k)} :
-- imply
  dist (faceEmbedding k (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) (vertexEmbedding k (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) ≤ mesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.FullSquareCoordinateEmbeddingCompatibility.incidenceDistance C k e

/--
[fullSquareScaledEmbedding_incidenceDistance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullSquareScaledEmbedding_incidenceDistance_eq
  {N : Nat → Nat}
  {mesh : Nat → Real}
  {k : Nat}
  {e : FKIsingSquareInteriorRadialIncidence (N k) (hN k)}
-- given
  (hN : ∀ k, 0 < N k)
  (hmesh : ∀ k, 0 ≤ mesh k) :
-- imply
  dist (fullSquareScaledFaceEmbedding (N k) (mesh k) (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) ≤ mesh k := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledEmbedding_incidenceDistance N hN mesh hmesh k e

/--
[vertexSampled_boundaryConsistencyError_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexSampled_boundaryConsistencyError_le_eq
  {n : Nat}
  {embedding : FKIsingSquareFullVertexNode n → Complex}
  {Phi : Complex → Complex}
  {bound : Real}
-- given
  (hn : 0 < n)
  (hbound : 0 ≤ bound)
  (hfixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x → |0 - (Phi (embedding x)).im| ≤ bound) :
-- imply
  vertexBoundaryConsistencyError n hn (vertexSampledImaginaryTarget n embedding Phi) ≤ bound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSampled_boundaryConsistencyError_le n hn embedding Phi bound hbound hfixed

/--
[faceSampled_boundaryConsistencyError_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceSampled_boundaryConsistencyError_le_eq
  {n : Nat}
  {embedding : FKIsingSquareFullFaceNode n → Complex}
  {Phi : Complex → Complex}
  {bound : Real}
-- given
  (hn : 0 < n)
  (hbound : 0 ≤ bound)
  (hfixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c → |1 - (Phi (embedding c)).im| ≤ bound) :
-- imply
  faceBoundaryConsistencyError n hn (faceSampledImaginaryTarget n embedding Phi) ≤ bound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSampled_boundaryConsistencyError_le n hn embedding Phi bound hbound hfixed

/--
[vertexSampled_boundaryConsistencyError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexSampled_boundaryConsistencyError_eq_zero_eq
  {n : Nat}
  {embedding : FKIsingSquareFullVertexNode n → Complex}
  {Phi : Complex → Complex}
-- given
  (hn : 0 < n)
  (hfixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x → (Phi (embedding x)).im = 0) :
-- imply
  vertexBoundaryConsistencyError n hn (vertexSampledImaginaryTarget n embedding Phi) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSampled_boundaryConsistencyError_eq_zero n hn embedding Phi hfixed

/--
[faceSampled_boundaryConsistencyError_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceSampled_boundaryConsistencyError_eq_zero_eq
  {n : Nat}
  {embedding : FKIsingSquareFullFaceNode n → Complex}
  {Phi : Complex → Complex}
-- given
  (hn : 0 < n)
  (hfixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c → (Phi (embedding c)).im = 1) :
-- imply
  faceBoundaryConsistencyError n hn (faceSampledImaginaryTarget n embedding Phi) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSampled_boundaryConsistencyError_eq_zero n hn embedding Phi hfixed

/--
[vertexSampled_targetResidual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexSampled_targetResidual_le_eq
  {n : Nat}
  {embedding : FKIsingSquareFullVertexNode n → Complex}
  {Phi : Complex → Complex}
  {bound : Real}
-- given
  (hbound : 0 ≤ bound)
  (hrobin : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y ↦ (Phi (embedding y)).im) x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (Phi (embedding x)).im)| ≤ bound) :
-- imply
  vertexTargetResidual n (vertexSampledImaginaryTarget n embedding Phi) ≤ bound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSampled_targetResidual_le n embedding Phi bound hbound hrobin

/--
[faceSampled_targetResidual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceSampled_targetResidual_le_eq
  {n : Nat}
  {embedding : FKIsingSquareFullFaceNode n → Complex}
  {Phi : Complex → Complex}
  {bound : Real}
-- given
  (hbound : 0 ≤ bound)
  (hrobin : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d ↦ (Phi (embedding d)).im) c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - (Phi (embedding c)).im)| ≤ bound) :
-- imply
  faceTargetResidual n (faceSampledImaginaryTarget n embedding Phi) ≤ bound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSampled_targetResidual_le n embedding Phi bound hbound hrobin

/--
[fullVertexGhostMultiplicity_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullVertexGhostMultiplicity_le_three_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  fkIsingSquareFullVertexGhostMultiplicity n x ≤ 3 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexGhostMultiplicity_le_three n x

/--
[fullFaceGhostMultiplicity_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullFaceGhostMultiplicity_le_one_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  fkIsingSquareFullFaceGhostMultiplicity n c ≤ 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullFaceGhostMultiplicity_le_one n c

/--
[vertexGhostRate_le_threeCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexGhostRate_le_threeCoefficient_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x ≤ 3 * isingFermionicGhostCoefficient := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexGhostRate_le_threeCoefficient n x

/--
[faceGhostRate_le_coefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceGhostRate_le_coefficient_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c ≤ isingFermionicGhostCoefficient := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhostRate_le_coefficient n c

/--
[vertexSampled_robinResidual_le_of_laplacian_and_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexSampled_robinResidual_le_of_laplacian_and_trace_eq
  {n : Nat}
  {embedding : FKIsingSquareFullVertexNode n → Complex}
  {Phi : Complex → Complex}
  {laplacianBound traceBound : Real}
-- given
  (htrace_nonneg : 0 ≤ traceBound)
  (hlaplacian : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y ↦ (Phi (embedding y)).im) x| ≤ laplacianBound)
  (htrace : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → 0 < fkIsingSquareFullVertexGhostMultiplicity n x → |1 - (Phi (embedding x)).im| ≤ traceBound) :
-- imply
  ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y ↦ (Phi (embedding y)).im) x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - (Phi (embedding x)).im)| ≤ laplacianBound + (3 * isingFermionicGhostCoefficient) * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSampled_robinResidual_le_of_laplacian_and_trace n embedding Phi laplacianBound traceBound htrace_nonneg hlaplacian htrace

/--
[faceSampled_robinResidual_le_of_laplacian_and_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceSampled_robinResidual_le_of_laplacian_and_trace_eq
  {n : Nat}
  {embedding : FKIsingSquareFullFaceNode n → Complex}
  {Phi : Complex → Complex}
  {laplacianBound traceBound : Real}
-- given
  (htrace_nonneg : 0 ≤ traceBound)
  (hlaplacian : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d ↦ (Phi (embedding d)).im) c| ≤ laplacianBound)
  (htrace : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → 0 < fkIsingSquareFullFaceGhostMultiplicity n c → |0 - (Phi (embedding c)).im| ≤ traceBound) :
-- imply
  ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d ↦ (Phi (embedding d)).im) c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - (Phi (embedding c)).im)| ≤ laplacianBound + isingFermionicGhostCoefficient * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSampled_robinResidual_le_of_laplacian_and_trace n embedding Phi laplacianBound traceBound htrace_nonneg hlaplacian htrace

/--
[vertexSampled_targetResidual_le_of_laplacian_and_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexSampled_targetResidual_le_of_laplacian_and_trace_eq
  {n : Nat}
  {embedding : FKIsingSquareFullVertexNode n → Complex}
  {Phi : Complex → Complex}
  {laplacianBound traceBound : Real}
-- given
  (hlaplacian_nonneg : 0 ≤ laplacianBound)
  (htrace_nonneg : 0 ≤ traceBound)
  (hlaplacian : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y ↦ (Phi (embedding y)).im) x| ≤ laplacianBound)
  (htrace : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → 0 < fkIsingSquareFullVertexGhostMultiplicity n x → |1 - (Phi (embedding x)).im| ≤ traceBound) :
-- imply
  vertexTargetResidual n (vertexSampledImaginaryTarget n embedding Phi) ≤ laplacianBound + (3 * isingFermionicGhostCoefficient) * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSampled_targetResidual_le_of_laplacian_and_trace n embedding Phi laplacianBound traceBound hlaplacian_nonneg htrace_nonneg hlaplacian htrace

/--
[faceSampled_targetResidual_le_of_laplacian_and_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceSampled_targetResidual_le_of_laplacian_and_trace_eq
  {n : Nat}
  {embedding : FKIsingSquareFullFaceNode n → Complex}
  {Phi : Complex → Complex}
  {laplacianBound traceBound : Real}
-- given
  (hlaplacian_nonneg : 0 ≤ laplacianBound)
  (htrace_nonneg : 0 ≤ traceBound)
  (hlaplacian : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d ↦ (Phi (embedding d)).im) c| ≤ laplacianBound)
  (htrace : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → 0 < fkIsingSquareFullFaceGhostMultiplicity n c → |0 - (Phi (embedding c)).im| ≤ traceBound) :
-- imply
  faceTargetResidual n (faceSampledImaginaryTarget n embedding Phi) ≤ laplacianBound + isingFermionicGhostCoefficient * traceBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSampled_targetResidual_le_of_laplacian_and_trace n embedding Phi laplacianBound traceBound hlaplacian_nonneg htrace_nonneg hlaplacian htrace

/--
[vertexSampled_targetResidual_le_of_exact_free_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexSampled_targetResidual_le_of_exact_free_trace_eq
  {n : Nat}
  {embedding : FKIsingSquareFullVertexNode n → Complex}
  {Phi : Complex → Complex}
  {laplacianBound : Real}
-- given
  (hlaplacian_nonneg : 0 ≤ laplacianBound)
  (hlaplacian : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y ↦ (Phi (embedding y)).im) x| ≤ laplacianBound)
  (hfree : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x → 0 < fkIsingSquareFullVertexGhostMultiplicity n x → (Phi (embedding x)).im = 1) :
-- imply
  vertexTargetResidual n (vertexSampledImaginaryTarget n embedding Phi) ≤ laplacianBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSampled_targetResidual_le_of_exact_free_trace n embedding Phi laplacianBound hlaplacian_nonneg hlaplacian hfree

/--
[faceSampled_targetResidual_le_of_exact_free_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceSampled_targetResidual_le_of_exact_free_trace_eq
  {n : Nat}
  {embedding : FKIsingSquareFullFaceNode n → Complex}
  {Phi : Complex → Complex}
  {laplacianBound : Real}
-- given
  (hlaplacian_nonneg : 0 ≤ laplacianBound)
  (hlaplacian : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d ↦ (Phi (embedding d)).im) c| ≤ laplacianBound)
  (hfree : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c → 0 < fkIsingSquareFullFaceGhostMultiplicity n c → (Phi (embedding c)).im = 0) :
-- imply
  faceTargetResidual n (faceSampledImaginaryTarget n embedding Phi) ≤ laplacianBound := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSampled_targetResidual_le_of_exact_free_trace n embedding Phi laplacianBound hlaplacian_nonneg hlaplacian hfree

/--
[fullVertex_neighbor_card_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma fullVertex_neighbor_card_le_four_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  Nat.card ↑((fkIsingSquareFullVertexGraph n).neighborSet x) ≤ 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertex_neighbor_card_le_four n x

/--
[vertexQuadraticBarrier_laplacian_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexQuadraticBarrier_laplacian_le_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fkIsingSquareBoxQuadraticBarrier n) x ≤ 2 * (n : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexQuadraticBarrier_laplacian_le n x

/--
[vertexBarrierOffset_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexBarrierOffset_nonneg_eq
  {n : Nat} :
-- imply
  0 ≤ vertexBarrierOffset n := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBarrierOffset_nonneg n

/--
[vertexExplicitPoissonBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexExplicitPoissonBarrier_nonneg_eq
  {n : Nat} :
-- imply
  ∀ x, 0 ≤ vertexExplicitPoissonBarrier n x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexExplicitPoissonBarrier_nonneg n

/--
[vertexExplicitPoissonBarrier_le_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexExplicitPoissonBarrier_le_bound_eq
  {n : Nat} :
-- imply
  ∀ x, vertexExplicitPoissonBarrier n x ≤ vertexExplicitPoissonBarrierBound n := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexExplicitPoissonBarrier_le_bound n

/--
[vertexExplicitPoissonBarrier_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexExplicitPoissonBarrier_laplacian_eq
  {n : Nat}
  {x : Option (FKIsingSquareFullVertexNode n)}
-- given
  (hn : 0 < n)
  (hx : ¬ vertexDirichletBoundary n x) :
-- imply
  isingFiniteWeightedLaplacian (vertexGhostConductance n) (vertexExplicitPoissonBarrier n) x ≤ -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexExplicitPoissonBarrier_laplacian n hn x hx

/--
[vertexPoissonBarrier_le_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexPoissonBarrier_le_explicit_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  ∀ x, isingFiniteWeightedPoissonBarrier (vertexGhostGraph n) (vertexGhostConductance n) (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n) (vertexGhostConductance_pos_of_adj n) (vertexGhost_reaches_boundary n) x ≤ vertexExplicitPoissonBarrier n x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPoissonBarrier_le_explicit n hn

/--
[vertexPoissonBarrierBound_le_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexPoissonBarrierBound_le_explicit_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  vertexPoissonBarrierBound n ≤ vertexExplicitPoissonBarrierBound n := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPoissonBarrierBound_le_explicit n hn

/--
[faceRowPoissonBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceRowPoissonBarrier_nonneg_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  0 ≤ faceRowPoissonBarrier n c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceRowPoissonBarrier_nonneg n c

/--
[faceRowPoissonBarrier_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceRowPoissonBarrier_le_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  faceRowPoissonBarrier n c ≤ faceExplicitPoissonBarrierBound n := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceRowPoissonBarrier_le n c

/--
[faceExplicitPoissonBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceExplicitPoissonBarrier_nonneg_eq
  {n : Nat} :
-- imply
  ∀ c, 0 ≤ faceExplicitPoissonBarrier n c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceExplicitPoissonBarrier_nonneg n

/--
[faceExplicitPoissonBarrier_le_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceExplicitPoissonBarrier_le_bound_eq
  {n : Nat} :
-- imply
  ∀ c, faceExplicitPoissonBarrier n c ≤ faceExplicitPoissonBarrierBound n := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceExplicitPoissonBarrier_le_bound n

/--
[face_neighborFinset_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma face_neighborFinset_left_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
  [Fintype ↑((fkIsingSquareFullFaceGraph n).neighborSet c)]
-- given
  (hleft : c.1.1 = 0)
  (heast : c.1.1 + 1 < 2 * n)
  (hnorth : c.2.1 + 1 < 2 * n)
  (hsouth : 0 < c.2.1) :
-- imply
  (fkIsingSquareFullFaceGraph n).neighborFinset c = {faceEastNeighbor n c heast, faceNorthNeighbor n c hnorth, faceSouthNeighbor n c hsouth} := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.face_neighborFinset_left n c hleft heast hnorth hsouth

/--
[faceColumnFunction_laplacian_of_not_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceColumnFunction_laplacian_of_not_fixed_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (F : Nat -> Real)
  (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => F d.1.1) c = if c.1.1 = 0 then F 1 - F 0 else F (c.1.1 + 1) + F (c.1.1 - 1) - 2 * F c.1.1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceColumnFunction_laplacian_of_not_fixed n F c hc

/--
[faceRowFunction_laplacian_of_not_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceRowFunction_laplacian_of_not_fixed_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (F : Nat -> Real)
  (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => F d.2.1) c = F (c.2.1 + 1) + F (c.2.1 - 1) - 2 * F c.2.1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceRowFunction_laplacian_of_not_fixed n F c hc

/--
[faceRowPoissonBarrier_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceRowPoissonBarrier_laplacian_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (faceRowPoissonBarrier n) c = -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceRowPoissonBarrier_laplacian n c hc

/--
[faceExplicitPoissonBarrier_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceExplicitPoissonBarrier_laplacian_eq
  {n : Nat}
  {c : Option (FKIsingSquareFullFaceNode n)}
-- given
  (hc : ¬ faceDirichletBoundary n c) :
-- imply
  isingFiniteWeightedLaplacian (faceGhostConductance n) (faceExplicitPoissonBarrier n) c ≤ -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceExplicitPoissonBarrier_laplacian n c hc

/--
[facePoissonBarrier_le_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma facePoissonBarrier_le_explicit_eq
  {n : Nat} :
-- imply
  ∀ c, isingFiniteWeightedPoissonBarrier (faceGhostGraph n) (faceGhostConductance n) (faceDirichletBoundary n) (faceGhostConductance_nonneg n) (faceGhostConductance_pos_of_adj n) (faceGhost_reaches_boundary n) c ≤ faceExplicitPoissonBarrier n c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePoissonBarrier_le_explicit n

/--
[facePoissonBarrierBound_le_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma facePoissonBarrierBound_le_explicit_eq
  {n : Nat} :
-- imply
  facePoissonBarrierBound n ≤ faceExplicitPoissonBarrierBound n := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePoissonBarrierBound_le_explicit n

/--
[vertexBarrierGrowthConstant_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexBarrierGrowthConstant_nonneg_eq :
-- imply
  0 ≤ vertexBarrierGrowthConstant := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBarrierGrowthConstant_nonneg

/--
[half_le_vertexBarrierGrowthConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma half_le_vertexBarrierGrowthConstant_eq :
-- imply
  (1 / 2 : Real) ≤ vertexBarrierGrowthConstant := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.half_le_vertexBarrierGrowthConstant

/--
[vertexExplicitPoissonBarrierBound_le_growth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexExplicitPoissonBarrierBound_le_growth_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  vertexExplicitPoissonBarrierBound n ≤ vertexBarrierGrowthConstant * (n : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexExplicitPoissonBarrierBound_le_growth n hn

/--
[vertexPoissonBarrierBound_le_growth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexPoissonBarrierBound_le_growth_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  vertexPoissonBarrierBound n ≤ vertexBarrierGrowthConstant * (n : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPoissonBarrierBound_le_growth n hn

/--
[facePoissonBarrierBound_le_growth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma facePoissonBarrierBound_le_growth_eq
  {n : Nat} :
-- imply
  facePoissonBarrierBound n ≤ vertexBarrierGrowthConstant * (n : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.facePoissonBarrierBound_le_growth n

/--
[vertexTargetConsistencyError_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma vertexTargetConsistencyError_nonneg_eq
  {n : Nat}
  {target : Option (FKIsingSquareFullVertexNode n) → Real}
-- given
  (hn : 0 < n) :
-- imply
  0 ≤ vertexTargetConsistencyError n hn target := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexTargetConsistencyError_nonneg n hn target

/--
[faceTargetConsistencyError_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma faceTargetConsistencyError_nonneg_eq
  {n : Nat}
  {target : Option (FKIsingSquareFullFaceNode n) → Real}
-- given
  (hn : 0 < n) :
-- imply
  0 ≤ faceTargetConsistencyError n hn target := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceTargetConsistencyError_nonneg n hn target

/--
[sampledWeightedConsistency_tendsto_of_quadraticRates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma sampledWeightedConsistency_tendsto_of_quadraticRates_eq
  {N : Nat → Nat}
  {Phi : Complex → Complex}
  {boundaryRate residualRate : Nat → Real}
-- given
  (hN : ∀ k, 0 < N k)
  (vertexEmbedding : ∀ k, FKIsingSquareFullVertexNode (N k) → Complex)
  (faceEmbedding : ∀ k, FKIsingSquareFullFaceNode (N k) → Complex)
  (hboundary_nonneg : ∀ k, 0 ≤ boundaryRate k)
  (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
  (hvertexFixed : ∀ k x, fkIsingSquareFullVertexFixedBoundary (N k) x → |0 - (Phi (vertexEmbedding k x)).im| ≤ boundaryRate k)
  (hfaceFixed : ∀ k c, fkIsingSquareFullFaceFixedBoundary (N k) c → |1 - (Phi (faceEmbedding k c)).im| ≤ boundaryRate k)
  (hvertexRobin : ∀ k x, ¬ fkIsingSquareFullVertexFixedBoundary (N k) x → |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y ↦ (Phi (vertexEmbedding k y)).im) x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity (N k)) x * (1 - (Phi (vertexEmbedding k x)).im)| ≤ residualRate k)
  (hfaceRobin : ∀ k c, ¬ fkIsingSquareFullFaceFixedBoundary (N k) c → |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d ↦ (Phi (faceEmbedding k d)).im) c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity (N k)) c * (0 - (Phi (faceEmbedding k c)).im)| ≤ residualRate k)
  (hboundary_tendsto : Tendsto boundaryRate atTop (nhds 0))
  (hscaledResidual_tendsto : Tendsto (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
-- imply
  Tendsto (fun k ↦ max (vertexTargetConsistencyError (N k) (hN k) (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi)) (faceTargetConsistencyError (N k) (hN k) (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi))) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.sampledWeightedConsistency_tendsto_of_quadraticRates N hN vertexEmbedding faceEmbedding Phi boundaryRate residualRate hboundary_nonneg hresidual_nonneg hvertexFixed hfaceFixed hvertexRobin hfaceRobin hboundary_tendsto hscaledResidual_tendsto

/--
[sampledWeightedConsistency_tendsto_of_meshAndQuadraticResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma sampledWeightedConsistency_tendsto_of_meshAndQuadraticResidual_eq
  {N : Nat → Nat}
  {Phi : Complex → Complex}
  {mesh residualRate : Nat → Real}
  {L : Real}
-- given
  (hN : ∀ k, 0 < N k)
  (vertexEmbedding : ∀ k, FKIsingSquareFullVertexNode (N k) → Complex)
  (faceEmbedding : ∀ k, FKIsingSquareFullFaceNode (N k) → Complex)
  (hmesh_nonneg : ∀ k, 0 ≤ mesh k)
  (hL : 0 ≤ L)
  (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
  (hvertexFixed : ∀ k x, fkIsingSquareFullVertexFixedBoundary (N k) x → |0 - (Phi (vertexEmbedding k x)).im| ≤ L * mesh k)
  (hfaceFixed : ∀ k c, fkIsingSquareFullFaceFixedBoundary (N k) c → |1 - (Phi (faceEmbedding k c)).im| ≤ L * mesh k)
  (hvertexRobin : ∀ k x, ¬ fkIsingSquareFullVertexFixedBoundary (N k) x → |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y ↦ (Phi (vertexEmbedding k y)).im) x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity (N k)) x * (1 - (Phi (vertexEmbedding k x)).im)| ≤ residualRate k)
  (hfaceRobin : ∀ k c, ¬ fkIsingSquareFullFaceFixedBoundary (N k) c → |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d ↦ (Phi (faceEmbedding k d)).im) c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity (N k)) c * (0 - (Phi (faceEmbedding k c)).im)| ≤ residualRate k)
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
  (hscaledResidual_tendsto : Tendsto (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
-- imply
  Tendsto (fun k ↦ max (vertexTargetConsistencyError (N k) (hN k) (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi)) (faceTargetConsistencyError (N k) (hN k) (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi))) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.sampledWeightedConsistency_tendsto_of_meshAndQuadraticResidual N hN vertexEmbedding faceEmbedding Phi mesh residualRate L hmesh_nonneg hL hresidual_nonneg hvertexFixed hfaceFixed hvertexRobin hfaceRobin hmesh_tendsto hscaledResidual_tendsto

/--
[physicalIncidence_sampledTarget_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma physicalIncidence_sampledTarget_error_le_eq
  {n : Nat}
  {vertexEmbedding : FKIsingSquareFullVertexNode n → Complex}
  {faceEmbedding : FKIsingSquareFullFaceNode n → Complex}
  {Phi : Complex → Complex}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
  {target : Real}
-- given
  (hn : 0 < n) :
-- imply
  |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) - target| ≤ max (vertexTargetConsistencyError n hn (vertexSampledImaginaryTarget n vertexEmbedding Phi)) (faceTargetConsistencyError n hn (faceSampledImaginaryTarget n faceEmbedding Phi)) + max |(Phi (vertexEmbedding (fkIsingSquareInteriorRadialEndpoint n hn e))).im - target| |(Phi (faceEmbedding (fkIsingSquareFullFaceOfRadialIncidence n hn e))).im - target| ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) - target| ≤ max (vertexTargetConsistencyError n hn (vertexSampledImaginaryTarget n vertexEmbedding Phi)) (faceTargetConsistencyError n hn (faceSampledImaginaryTarget n faceEmbedding Phi)) + max |(Phi (vertexEmbedding (fkIsingSquareInteriorRadialEndpoint n hn e))).im - target| |(Phi (faceEmbedding (fkIsingSquareFullFaceOfRadialIncidence n hn e))).im - target| := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_sampledTarget_error_le n hn vertexEmbedding faceEmbedding Phi e target

/--
[physicalIncidence_uniform_convergence_of_sampledConsistency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma physicalIncidence_uniform_convergence_of_sampledConsistency_eq
  {N : Nat → Nat}
  {Phi : Complex → Complex}
  {vertexMismatch faceMismatch : Nat → Real}
-- given
  (hN : ∀ k, 0 < N k)
  (vertexEmbedding : ∀ k, FKIsingSquareFullVertexNode (N k) → Complex)
  (faceEmbedding : ∀ k, FKIsingSquareFullFaceNode (N k) → Complex)
  (incidenceTarget : ∀ k, FKIsingSquareInteriorRadialIncidence (N k) (hN k) → Real)
  (hvertexMismatch : ∀ k e, |(Phi (vertexEmbedding k (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im - incidenceTarget k e| ≤ vertexMismatch k)
  (hfaceMismatch : ∀ k e, |(Phi (faceEmbedding k (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im - incidenceTarget k e| ≤ faceMismatch k)
  (hconsistency : Tendsto (fun k ↦ max (vertexTargetConsistencyError (N k) (hN k) (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi)) (faceTargetConsistencyError (N k) (hN k) (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi))) atTop (nhds 0))
  (hvertexMismatch_tendsto : Tendsto vertexMismatch atTop (nhds 0))
  (hfaceMismatch_tendsto : Tendsto faceMismatch atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop, ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - incidenceTarget k e| < eta ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - incidenceTarget k e| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_uniform_convergence_of_sampledConsistency N hN vertexEmbedding faceEmbedding Phi incidenceTarget vertexMismatch faceMismatch hvertexMismatch hfaceMismatch hconsistency hvertexMismatch_tendsto hfaceMismatch_tendsto

/--
[physicalIncidence_uniform_convergence_of_lipschitzSamples](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma physicalIncidence_uniform_convergence_of_lipschitzSamples_eq
  {N : Nat → Nat}
  {Phi : Complex → Complex}
  {lipschitzConstant : NNReal}
  {mesh : Nat → Real}
  {embeddingCompatibility : FullSquareCoordinateEmbeddingCompatibility N vertexEmbedding faceEmbedding mesh}
-- given
  (hN : ∀ k, 0 < N k)
  (vertexEmbedding : ∀ k, FKIsingSquareFullVertexNode (N k) → Complex)
  (faceEmbedding : ∀ k, FKIsingSquareFullFaceNode (N k) → Complex)
  (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
  (hconsistency : Tendsto (fun k ↦ max (vertexTargetConsistencyError (N k) (hN k) (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi)) (faceTargetConsistencyError (N k) (hN k) (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi))) atTop (nhds 0))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop, ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - (Phi (vertexEmbedding k (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - (Phi (vertexEmbedding k (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_uniform_convergence_of_lipschitzSamples N hN vertexEmbedding faceEmbedding Phi lipschitzConstant hPhi mesh embeddingCompatibility hconsistency hmesh_tendsto

/--
[physicalIncidence_uniform_convergence_of_meshAndQuadraticResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma physicalIncidence_uniform_convergence_of_meshAndQuadraticResidual_eq
  {N : Nat → Nat}
  {Phi : Complex → Complex}
  {mesh residualRate : Nat → Real}
  {boundaryL : Real}
  {lipschitzConstant : NNReal}
  {embeddingCompatibility : FullSquareCoordinateEmbeddingCompatibility N vertexEmbedding faceEmbedding mesh}
-- given
  (hN : ∀ k, 0 < N k)
  (vertexEmbedding : ∀ k, FKIsingSquareFullVertexNode (N k) → Complex)
  (faceEmbedding : ∀ k, FKIsingSquareFullFaceNode (N k) → Complex)
  (hmesh_nonneg : ∀ k, 0 ≤ mesh k)
  (hboundaryL : 0 ≤ boundaryL)
  (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
  (hvertexFixed : ∀ k x, fkIsingSquareFullVertexFixedBoundary (N k) x → |0 - (Phi (vertexEmbedding k x)).im| ≤ boundaryL * mesh k)
  (hfaceFixed : ∀ k c, fkIsingSquareFullFaceFixedBoundary (N k) c → |1 - (Phi (faceEmbedding k c)).im| ≤ boundaryL * mesh k)
  (hvertexRobin : ∀ k x, ¬ fkIsingSquareFullVertexFixedBoundary (N k) x → |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y ↦ (Phi (vertexEmbedding k y)).im) x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity (N k)) x * (1 - (Phi (vertexEmbedding k x)).im)| ≤ residualRate k)
  (hfaceRobin : ∀ k c, ¬ fkIsingSquareFullFaceFixedBoundary (N k) c → |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d ↦ (Phi (faceEmbedding k d)).im) c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity (N k)) c * (0 - (Phi (faceEmbedding k c)).im)| ≤ residualRate k)
  (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
  (hscaledResidual_tendsto : Tendsto (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop, ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - (Phi (vertexEmbedding k (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - (Phi (vertexEmbedding k (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_uniform_convergence_of_meshAndQuadraticResidual N hN vertexEmbedding faceEmbedding Phi mesh residualRate boundaryL lipschitzConstant hmesh_nonneg hboundaryL hresidual_nonneg hvertexFixed hfaceFixed hvertexRobin hfaceRobin hPhi embeddingCompatibility hmesh_tendsto hscaledResidual_tendsto

/--
[physicalIncidence_uniform_convergence_of_scaledMeshAndQuadraticResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma physicalIncidence_uniform_convergence_of_scaledMeshAndQuadraticResidual_eq
  {N : Nat → Nat}
  {Phi : Complex → Complex}
  {mesh residualRate : Nat → Real}
  {boundaryL : Real}
  {lipschitzConstant : NNReal}
-- given
  (hN : ∀ k, 0 < N k)
  (hmesh_nonneg : ∀ k, 0 ≤ mesh k)
  (hboundaryL : 0 ≤ boundaryL)
  (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
  (hvertexFixed : ∀ k x, fkIsingSquareFullVertexFixedBoundary (N k) x → |0 - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| ≤ boundaryL * mesh k)
  (hfaceFixed : ∀ k c, fkIsingSquareFullFaceFixedBoundary (N k) c → |1 - (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| ≤ boundaryL * mesh k)
  (hvertexRobin : ∀ k x, ¬ fkIsingSquareFullVertexFixedBoundary (N k) x → |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y ↦ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x + isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity (N k)) x * (1 - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im)| ≤ residualRate k)
  (hfaceRobin : ∀ k c, ¬ fkIsingSquareFullFaceFixedBoundary (N k) c → |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d ↦ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c + isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity (N k)) c * (0 - (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im)| ≤ residualRate k)
  (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
  (hscaledResidual_tendsto : Tendsto (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop, ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_uniform_convergence_of_scaledMeshAndQuadraticResidual N hN Phi mesh residualRate boundaryL lipschitzConstant hmesh_nonneg hboundaryL hresidual_nonneg hvertexFixed hfaceFixed hvertexRobin hfaceRobin hPhi hmesh_tendsto hscaledResidual_tendsto

/--
[physicalIncidence_uniform_convergence_of_scaledExactBoundaryAndLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean)
-/
@[path]
private lemma physicalIncidence_uniform_convergence_of_scaledExactBoundaryAndLaplacian_eq
  {N : Nat → Nat}
  {Phi : Complex → Complex}
  {mesh laplacianRate : Nat → Real}
  {lipschitzConstant : NNReal}
-- given
  (hN : ∀ k, 0 < N k)
  (hmesh_nonneg : ∀ k, 0 ≤ mesh k)
  (hlaplacian_nonneg : ∀ k, 0 ≤ laplacianRate k)
  (hvertexFixed : ∀ k x, fkIsingSquareFullVertexFixedBoundary (N k) x → (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
  (hfaceFixed : ∀ k c, fkIsingSquareFullFaceFixedBoundary (N k) c → (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
  (hvertexFree : ∀ k x, ¬ fkIsingSquareFullVertexFixedBoundary (N k) x → 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x → (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
  (hfaceFree : ∀ k c, ¬ fkIsingSquareFullFaceFixedBoundary (N k) c → 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c → (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
  (hvertexLaplacian : ∀ k x, ¬ fkIsingSquareFullVertexFixedBoundary (N k) x → |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y ↦ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x| ≤ laplacianRate k)
  (hfaceLaplacian : ∀ k c, ¬ fkIsingSquareFullFaceFixedBoundary (N k) c → |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d ↦ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c| ≤ laplacianRate k)
  (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
  (hscaledLaplacian_tendsto : Tendsto (fun k ↦ laplacianRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop, ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_uniform_convergence_of_scaledExactBoundaryAndLaplacian N hN Phi mesh laplacianRate lipschitzConstant hmesh_nonneg hlaplacian_nonneg hvertexFixed hfaceFixed hvertexFree hfaceFree hvertexLaplacian hfaceLaplacian hPhi hmesh_tendsto hscaledLaplacian_tendsto


-- created on 2026-10-23
