import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredDiagonalScalingLimit
open Filter Set Topology StatMech StatMech.Universality StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[scalingLimit_of_continuous_compactHolder_denseIncidencePaths_of_root_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredDiagonalScalingLimit.lean)
-/
@[path]
private lemma scalingLimit_of_continuous_compactHolder_denseIncidencePaths_of_root_tendsto_eq
  {F : Nat → Complex → Complex}
  {Hholder : fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder F}
  {N : Nat → Nat}
  {hN : ∀ k, 0 < N k}
  {mesh bulkRate layerRate : Nat → Real}
  {target Phi : Complex → Complex}
  {D : FKIsingDenseIncidenceFamily N hN mesh}
  {Hrobin : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs N hN Phi mesh bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
-- given
  (hcontinuous : ∀ n, Continuous (F n))
  (P : FKIsingDenseIncidencePrimitivePathCompatibility (N := N) (hN := hN) (mesh := mesh) F D)
  (hPhiLip : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hMorera : ∀ (phi psi : Nat → Nat) (f : Complex → Complex), StrictMono phi → StrictMono psi → TendstoLocallyUniformlyOn (fun n ↦ F (phi (psi n))) f atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U → Complex.IsConservativeOn f fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hroot : Tendsto (fun n ↦ F n fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
-- imply
  TendstoLocallyUniformlyOn F target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.scalingLimit_of_continuous_compactHolder_denseIncidencePaths_of_root_tendsto F hcontinuous Hholder target Phi D P Hrobin lipschitzConstant hPhiLip htarget htarget_ne hPhi hPhideriv E hMorera hroot

/--
[scalingLimit_of_centeredFourSectorDiagonal_denseIncidencePaths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredDiagonalScalingLimit.lean)
-/
@[path]
private lemma scalingLimit_of_centeredFourSectorDiagonal_denseIncidencePaths_eq
  {L : NNReal}
  {N0 : Nat}
  {N : Nat → Nat}
  {hN : ∀ k, 0 < N k}
  {mesh bulkRate layerRate : Nat → Real}
  {target Phi : Complex → Complex}
  {D : FKIsingDenseIncidenceFamily N hN mesh}
  {Hrobin : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs N hN Phi mesh bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
-- given
  (hN0 : 1 ≤ N0)
  (hdiag : ∀ q : Fin 4, ∀ k, N0 ≤ k → ∀ i j, isingCenteredRadialIndexSector (fkIsingExpandingSquareSide k) i j = q → FKIsingExpandingCenteredDiagonalCellBound L k i j)
  (P : FKIsingDenseIncidencePrimitivePathCompatibility (N := N) (hN := hN) (mesh := mesh) fkIsingExpandingBoundarySquareCenteredReflectedInterpolant D)
  (hPhiLip : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hbase : Tendsto (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) atTop (nhds (target 0))) :
-- imply
  TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.scalingLimit_of_centeredFourSectorDiagonal_denseIncidencePaths L N0 hN0 hdiag target Phi D P Hrobin lipschitzConstant hPhiLip htarget htarget_ne hPhi hPhideriv E hbase

/--
[scalingLimit_of_centeredFullCarrierTV_denseIncidencePaths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredDiagonalScalingLimit.lean)
-/
@[path]
private lemma scalingLimit_of_centeredFullCarrierTV_denseIncidencePaths_eq
  {N : Nat → Nat}
  {hN : ∀ k, 0 < N k}
  {mesh bulkRate layerRate : Nat → Real}
  {target Phi : Complex → Complex}
  {D : FKIsingDenseIncidenceFamily N hN mesh}
  {Hrobin : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs N hN Phi mesh bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
-- given
  (P : FKIsingDenseIncidencePrimitivePathCompatibility (N := N) (hN := hN) (mesh := mesh) fkIsingExpandingBoundarySquareCenteredReflectedInterpolant D)
  (hPhiLip : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hbase : Tendsto (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) atTop (nhds (target 0))) :
-- imply
  TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.scalingLimit_of_centeredFullCarrierTV_denseIncidencePaths target Phi D P Hrobin lipschitzConstant hPhiLip htarget htarget_ne hPhi hPhideriv E hbase

/--
[scalingLimit_of_centeredFullCarrierTV_canonicalRationalPaths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredDiagonalScalingLimit.lean)
-/
@[path]
private lemma scalingLimit_of_centeredFullCarrierTV_canonicalRationalPaths_eq
  {bulkRate layerRate : Nat → Real}
  {target Phi : Complex → Complex}
  {L : FKIsingCanonicalDensePrimitiveLocalInputs fkIsingExpandingBoundarySquareCenteredReflectedInterpolant}
  {Hrobin : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs fkIsingExpandingSquareSide fkIsingExpandingSquareSide_pos Phi fkIsingExpandingSquareScale bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
-- given
  (hPhiLip : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hbase : Tendsto (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) atTop (nhds (target 0))) :
-- imply
  TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.scalingLimit_of_centeredFullCarrierTV_canonicalRationalPaths target Phi L Hrobin lipschitzConstant hPhiLip htarget htarget_ne hPhi hPhideriv E hbase


-- created on 2026-10-23
