import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part3
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant_continuous_eq
  {k m : Nat}
-- given
  (hm : m ≤ fkIsingExpandingSquareSide k) :
-- imply
  Continuous (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant_continuous k m hm

/--
[fkIsingExpandingBoundarySquareRadial_embedding_dist_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareRadial_embedding_dist_lt_eq
  {k m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hm : m ≤ fkIsingExpandingSquareSide k) :
-- imply
  dist (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k (fkIsingExpandingBoundarySquareRadialDart k m hm i j s)) (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1) < fkIsingExpandingSquareScale k / 10 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareRadial_embedding_dist_lt k m hm i j s

/--
[fkIsingExpandingBoundarySquareRadial_normalizedObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareRadial_normalizedObservable_eq
  {k m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hm : m ≤ fkIsingExpandingSquareSide k) :
-- imply
  @FKIsingDobrushinDomain.normalizedFermionicObservable (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) (fkIsingExpandingBoundarySquareRadialDart k m hm i j s) = (fkIsingSquareBoundaryRestrictedDobrushinDomain (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) (.dart (fkIsingSquareRadialPatchEdge (fkIsingExpandingSquareSide k) m hm i j, s)) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareRadial_normalizedObservable k m hm i j s

/--
[fkIsingExpandingBoundarySquareRadial_projection_sample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareRadial_projection_sample_eq
  {k m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hm : m ≤ fkIsingExpandingSquareSide k) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) (fkIsingExpandingBoundarySquareRadialDart k m hm i j s)) (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1)) = @FKIsingDobrushinDomain.normalizedFermionicObservable (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) (fkIsingExpandingBoundarySquareRadialDart k m hm i j s) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareRadial_projection_sample k m hm i j s

/--
[fkIsingExpandingBoundarySquareRadial_projection_embedding_dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareRadial_projection_embedding_dist_le_eq
  {k m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
  {C alpha : NNReal}
-- given
  (hm : m ≤ fkIsingExpandingSquareSide k)
  (hholder : HolderWith C alpha (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm)) :
-- imply
  dist (isingProj (fkIsingSquareWiredDirectedTangent (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) (fkIsingExpandingBoundarySquareRadialDart k m hm i j s)) (fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant k m hm (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k (fkIsingExpandingBoundarySquareRadialDart k m hm i j s)))) (@FKIsingDobrushinDomain.normalizedFermionicObservable (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) (fkIsingExpandingBoundarySquareRadialDart k m hm i j s)) ≤ C * dist (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k (fkIsingExpandingBoundarySquareRadialDart k m hm i j s)) (fkIsingExpandingBoundarySquareRadialSamplePosition k i.1 j.1) ^ (alpha : Real) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareRadial_projection_embedding_dist_le k m hm i j s C alpha hholder

/--
[fullSquareScaledVertexEmbedding_dist_le_two_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fullSquareScaledVertexEmbedding_dist_le_two_abs_eq
  {n : Nat}
  {scale : Real}
  {x y : FKIsingSquareFullVertexNode n}
-- given
  (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
-- imply
  dist (fullSquareScaledVertexEmbedding n scale y) (fullSquareScaledVertexEmbedding n scale x) ≤ 2 * |scale| := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding_dist_le_two_abs n scale x y hxy

/--
[fullSquareScaledFaceEmbedding_dist_le_two_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fullSquareScaledFaceEmbedding_dist_le_two_abs_eq
  {n : Nat}
  {scale : Real}
  {c d : FKIsingSquareFullFaceNode n}
-- given
  (hcd : (fkIsingSquareFullFaceGraph n).Adj c d) :
-- imply
  dist (fullSquareScaledFaceEmbedding n scale d) (fullSquareScaledFaceEmbedding n scale c) ≤ 2 * |scale| := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFaceEmbedding_dist_le_two_abs n scale c d hcd

/--
[fullFace_neighbor_card_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fullFace_neighbor_card_le_four_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  Nat.card ↑((fkIsingSquareFullFaceGraph n).neighborSet c) ≤ 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullFace_neighbor_card_le_four n c

/--
[isingFiniteGraphLaplacian_abs_le_four_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma isingFiniteGraphLaplacian_abs_le_four_mul_eq
  [Fintype V]
  {G : SimpleGraph V}
  {f : V → Real}
  {x : V}
  {D : Real}
-- given
  (hD : 0 ≤ D)
  (hcard : Nat.card ↑(G.neighborSet x) ≤ 4)
  (hneighbor : ∀ y, G.Adj x y → |f y - f x| ≤ D) :
-- imply
  |isingFiniteGraphLaplacian G f x| ≤ 4 * D := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingFiniteGraphLaplacian_abs_le_four_mul G f x D hD hcard hneighbor

/--
[fullSquareScaledVertex_sampledLaplacian_le_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fullSquareScaledVertex_sampledLaplacian_le_lipschitz_eq
  {n : Nat}
  {scale : Real}
  {Phi : Complex → Complex}
  {L : NNReal}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hPhi : LipschitzWith L (fun z ↦ (Phi z).im)) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y ↦ (Phi (fullSquareScaledVertexEmbedding n scale y)).im) x| ≤ 8 * (L : Real) * |scale| := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertex_sampledLaplacian_le_lipschitz n scale Phi L hPhi x

/--
[fullSquareScaledFace_sampledLaplacian_le_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fullSquareScaledFace_sampledLaplacian_le_lipschitz_eq
  {n : Nat}
  {scale : Real}
  {Phi : Complex → Complex}
  {L : NNReal}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hPhi : LipschitzWith L (fun z ↦ (Phi z).im)) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d ↦ (Phi (fullSquareScaledFaceEmbedding n scale d)).im) c| ≤ 8 * (L : Real) * |scale| := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledFace_sampledLaplacian_le_lipschitz n scale Phi L hPhi c

/--
[fullSquareVertex_bulk_directions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fullSquareVertex_bulk_directions_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hfixed : ¬ fkIsingSquareFullVertexFixedBoundary n x)
  (hghost : fkIsingSquareFullVertexGhostMultiplicity n x = 0) :
-- imply
  fkIsingSquareDirectionAvailable n x .east ∧ fkIsingSquareDirectionAvailable n x .north ∧ fkIsingSquareDirectionAvailable n x .west ∧ fkIsingSquareDirectionAvailable n x .south := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareVertex_bulk_directions n x hfixed hghost

/--
[fullSquareFace_bulk_coordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma fullSquareFace_bulk_coordinates_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hfixed : ¬ fkIsingSquareFullFaceFixedBoundary n c)
  (hghost : fkIsingSquareFullFaceGhostMultiplicity n c = 0) :
-- imply
  c.1.1 + 1 < 2 * n ∧ c.2.1 + 1 < 2 * n ∧ 0 < c.1.1 ∧ 0 < c.2.1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareFace_bulk_coordinates n c hfixed hghost

/--
[PhysicalFourthOrderBulkData.vertexLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma vertexLaplacian_eq
  {N : Nat → Nat}
  {Phi : Complex → Complex}
  {mesh : Nat → Real}
  {H : PhysicalFourthOrderBulkData N Phi mesh}
  {k : Nat}
  {x : FKIsingSquareFullVertexNode (N k)}
-- given
  (hfixed : ¬ fkIsingSquareFullVertexFixedBoundary (N k) x)
  (hghost : fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k)) (fun y ↦ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im) x| ≤ (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalFourthOrderBulkData.vertexLaplacian H k x hfixed hghost

/--
[PhysicalFourthOrderBulkData.faceLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma faceLaplacian_eq
  {N : Nat → Nat}
  {Phi : Complex → Complex}
  {mesh : Nat → Real}
  {H : PhysicalFourthOrderBulkData N Phi mesh}
  {k : Nat}
  {c : FKIsingSquareFullFaceNode (N k)}
-- given
  (hfixed : ¬ fkIsingSquareFullFaceFixedBoundary (N k) c)
  (hghost : fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0) :
-- imply
  |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k)) (fun d ↦ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im) c| ≤ (H.boundOne + H.boundTwo) * |mesh k| ^ 4 / 12 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalFourthOrderBulkData.faceLaplacian H k c hfixed hghost

/--
[PhysicalSplitRobinConsistencyInputs.ofFourthOrderAndLipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma ofFourthOrderAndLipschitz_eq
  {N : Nat → Nat}
  {hN : ∀ k, 0 < N k}
  {Phi : Complex → Complex}
  {mesh : Nat → Real}
  {Hfourth : PhysicalFourthOrderBulkData N Phi mesh}
  {L : NNReal}
-- given
  (hPhi : LipschitzWith L (fun z ↦ (Phi z).im))
  (hmesh_nonneg : ∀ k, 0 ≤ mesh k)
  (hvertexFixed : ∀ k x, fkIsingSquareFullVertexFixedBoundary (N k) x → (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
  (hfaceFixed : ∀ k c, fkIsingSquareFullFaceFixedBoundary (N k) c → (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
  (hvertexFree : ∀ k x, ¬ fkIsingSquareFullVertexFixedBoundary (N k) x → 0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x → (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
  (hfaceFree : ∀ k c, ¬ fkIsingSquareFullFaceFixedBoundary (N k) c → 0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c → (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
  (hscaledFourth_tendsto : Tendsto (fun k ↦ |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0)) :
-- imply
  PhysicalSplitRobinConsistencyInputs N hN Phi mesh (fun k ↦ (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12) (fun k ↦ 8 * (L : Real) * |mesh k|) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs.ofFourthOrderAndLipschitz Hfourth L hPhi hmesh_nonneg hvertexFixed hfaceFixed hvertexFree hfaceFree hmesh_tendsto hscaledFourth_tendsto

/--
[PhysicalSplitRobinConsistencyInputs.primitive_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma primitive_convergence_eq
  {N : Nat → Nat}
  {hN : ∀ k, 0 < N k}
  {Phi : Complex → Complex}
  {mesh bulkRate layerRate : Nat → Real}
  {H : PhysicalSplitRobinConsistencyInputs N hN Phi mesh bulkRate layerRate}
  {lipschitzConstant : NNReal}
-- given
  (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop, ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs.primitive_convergence H lipschitzConstant hPhi

/--
[PhysicalRobinConsistencyInputs.primitive_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean)
-/
@[path]
private lemma primitive_convergence_eq_2
  {N : Nat → Nat}
  {hN : ∀ k, 0 < N k}
  {Phi : Complex → Complex}
  {mesh laplacianRate : Nat → Real}
  {H : PhysicalRobinConsistencyInputs N hN Phi mesh laplacianRate}
  {lipschitzConstant : NNReal}
-- given
  (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop, ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm (N k) (hN k)).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalRobinConsistencyInputs.primitive_convergence H lipschitzConstant hPhi


-- created on 2026-10-23
