import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidenceRootBound
open StatMech StatMech.Universality StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[StableFullMedialInterpolation.scalingLimit_of_compactHolder_denseIncidencePaths_of_root_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidenceRootBound.lean)
-/
@[path]
private lemma scalingLimit_of_compactHolder_denseIncidencePaths_of_root_tendsto_eq
  {tangent : ∀ n, fkIsingExpandingBoundarySquareCaratheodoryApproximation.M n → Complex}
  {I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.StableFullMedialInterpolation tangent}
  {Hholder : fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder I.interpolant}
  {N : Nat → Nat}
  {hN : ∀ k, 0 < N k}
  {mesh bulkRate layerRate : Nat → Real}
  {target Phi : Complex → Complex}
  {D : FKIsingDenseIncidenceFamily N hN mesh}
  {Hrobin : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs N hN Phi mesh bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
-- given
  (P : FKIsingDenseIncidencePrimitivePathCompatibility (N := N) (hN := hN) (mesh := mesh) I.interpolant D)
  (hPhiLip : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hMorera : ∀ (phi psi : Nat → Nat) (f : Complex → Complex), StrictMono phi → StrictMono psi → TendstoLocallyUniformlyOn (fun n ↦ I.interpolant (phi (psi n))) f atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U → Complex.IsConservativeOn f fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hroot : Tendsto (fun n ↦ I.interpolant n fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
-- imply
  TendstoLocallyUniformlyOn I.interpolant target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableFullMedialInterpolation.scalingLimit_of_compactHolder_denseIncidencePaths_of_root_tendsto I Hholder target Phi D P Hrobin lipschitzConstant hPhiLip htarget htarget_ne hPhi hPhideriv E hMorera hroot


-- created on 2026-10-23
