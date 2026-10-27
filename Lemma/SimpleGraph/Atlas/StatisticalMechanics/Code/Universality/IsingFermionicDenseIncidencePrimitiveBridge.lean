import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
open Filter Set Topology StatMech StatMech.Universality StatMech.Universality.FKIsingDenseIncidenceFamily StatMech.Universality.FKIsingDenseIncidencePrimitivePathCompatibility StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[discreteVertexPrimitive_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean)
-/
@[path]
private lemma discreteVertexPrimitive_tendsto_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {mesh : Nat -> Real}
  {Phi : Complex -> Complex}
  {bulkRate layerRate : Nat -> Real}
  {D : FKIsingDenseIncidenceFamily N hN mesh}
  {H : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs N hN Phi mesh bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {j : Nat}
-- given
  (hPhi : LipschitzWith lipschitzConstant (fun z => (Phi z).im)) :
-- imply
  Tendsto (fun k => D.discreteVertexPrimitive j k) atTop (nhds (Phi (D.point j)).im) := by
-- proof
  apply StatMech.Universality.FKIsingDenseIncidenceFamily.discreteVertexPrimitive_tendsto D H lipschitzConstant hPhi j

/--
[tendsto_canonical_sub_discrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean)
-/
@[path]
private lemma tendsto_canonical_sub_discrete_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {mesh : Nat -> Real}
  {F : Nat -> Complex -> Complex}
  {D : FKIsingDenseIncidenceFamily N hN mesh}
  {j : Nat}
-- given
  (P : FKIsingDenseIncidencePrimitivePathCompatibility (N := N) (hN := hN) (mesh := mesh) F D) :
-- imply
  Tendsto (fun k => (isingFermionicEntireSquarePrimitive (F k) (D.point j)).im - D.discreteVertexPrimitive j k) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingDenseIncidencePrimitivePathCompatibility.tendsto_canonical_sub_discrete P j

/--
[canonicalPrimitive_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean)
-/
@[path]
private lemma canonicalPrimitive_tendsto_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {mesh : Nat -> Real}
  {F : Nat -> Complex -> Complex}
  {D : FKIsingDenseIncidenceFamily N hN mesh}
  {Phi : Complex -> Complex}
  {bulkRate layerRate : Nat -> Real}
  {H : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs N hN Phi mesh bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {j : Nat}
-- given
  (P : FKIsingDenseIncidencePrimitivePathCompatibility (N := N) (hN := hN) (mesh := mesh) F D)
  (hPhi : LipschitzWith lipschitzConstant (fun z => (Phi z).im)) :
-- imply
  Tendsto (fun k => (isingFermionicEntireSquarePrimitive (F k) (D.point j)).im) atTop (nhds (Phi (D.point j)).im) := by
-- proof
  apply StatMech.Universality.FKIsingDenseIncidencePrimitivePathCompatibility.canonicalPrimitive_tendsto P H lipschitzConstant hPhi j

/--
[isingFermionicEntireSquarePrimitive_tendsto_at_of_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean)
-/
@[path]
private lemma isingFermionicEntireSquarePrimitive_tendsto_at_of_continuous_eq
  {F : Nat -> Complex -> Complex}
  {f : Complex -> Complex}
  {z : Complex}
-- given
  (hF : forall n, Continuous (F n))
  (hf : Continuous f)
  (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ) :
-- imply
  Tendsto (fun n => isingFermionicEntireSquarePrimitive (F n) z) atTop (nhds (isingFermionicEntireSquarePrimitive f z)) := by
-- proof
  apply StatMech.Universality.isingFermionicEntireSquarePrimitive_tendsto_at_of_continuous hF hf hlimit z

/--
[isingFermionicEntireSquarePrimitive_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean)
-/
@[path]
private lemma isingFermionicEntireSquarePrimitive_neg_eq
  {z : Complex}
-- given
  (f : Complex -> Complex) :
-- imply
  isingFermionicEntireSquarePrimitive (fun w => -f w) z = isingFermionicEntireSquarePrimitive f z := by
-- proof
  apply StatMech.Universality.isingFermionicEntireSquarePrimitive_neg f z

/--
[isingFermionicEntireSquarePrimitive_values_do_not_force_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean)
-/
@[path]
private lemma isingFermionicEntireSquarePrimitive_values_do_not_force_root_eq :
-- imply
  And (forall z, isingFermionicEntireSquarePrimitive (fun _ => (-1 : Complex)) z = isingFermionicEntireSquarePrimitive (fun _ => (1 : Complex)) z) (¬ Tendsto (fun _ : Nat => (-1 : Complex)) atTop (nhds (1 : Complex))) := by
-- proof
  apply StatMech.Universality.isingFermionicEntireSquarePrimitive_values_do_not_force_root

/--
[StableFullMedialInterpolation.scalingLimit_of_compactHolder_denseIncidencePaths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean)
-/
@[path]
private lemma scalingLimit_of_compactHolder_denseIncidencePaths_eq
  {tangent : forall n, fkIsingExpandingBoundarySquareCaratheodoryApproximation.M n -> Complex}
  {I : fkIsingExpandingBoundarySquareCaratheodoryApproximation.StableFullMedialInterpolation tangent}
  {Hholder : fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder I.interpolant}
  {B : Real}
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {mesh bulkRate layerRate : Nat -> Real}
  {D : FKIsingDenseIncidenceFamily N hN mesh}
  {Hrobin : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs N hN Phi mesh bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
-- given
  (hanchorBound : forall n, norm (I.interpolant n fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) <= B)
  (target Phi : Complex -> Complex)
  (P : FKIsingDenseIncidencePrimitivePathCompatibility (N := N) (hN := hN) (mesh := mesh) I.interpolant D)
  (hPhiLip : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hMorera : forall (phi psi : Nat -> Nat) (f : Complex -> Complex), StrictMono phi -> StrictMono psi -> TendstoLocallyUniformlyOn (fun n => I.interpolant (phi (psi n))) f atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U -> Complex.IsConservativeOn f fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hroot : Tendsto (fun n => I.interpolant n fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
-- imply
  TendstoLocallyUniformlyOn I.interpolant target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.StableFullMedialInterpolation.scalingLimit_of_compactHolder_denseIncidencePaths I Hholder B hanchorBound target Phi D P Hrobin lipschitzConstant hPhiLip htarget htarget_ne hPhi hPhideriv E hMorera hroot

/--
[BoundaryRadialTensorTentGeometry.scalingLimit_of_compactHolder_denseIncidencePaths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean)
-/
@[path]
private lemma scalingLimit_of_compactHolder_denseIncidencePaths_eq_2
  {G : BoundaryRadialTensorTentGeometry fkIsingExpandingBoundarySquareCaratheodoryApproximation}
  {Hholder : fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder (BoundaryRadialTensorTentGeometry.interpolant fkIsingExpandingBoundarySquareCaratheodoryApproximation G)}
  {B : Real}
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {mesh bulkRate layerRate : Nat -> Real}
  {D : FKIsingDenseIncidenceFamily N hN mesh}
  {Hrobin : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs N hN Phi mesh bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
-- given
  (hanchorBound : forall n, norm (BoundaryRadialTensorTentGeometry.interpolant fkIsingExpandingBoundarySquareCaratheodoryApproximation G n fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) <= B)
  (target Phi : Complex -> Complex)
  (P : FKIsingDenseIncidencePrimitivePathCompatibility (N := N) (hN := hN) (mesh := mesh) (BoundaryRadialTensorTentGeometry.interpolant fkIsingExpandingBoundarySquareCaratheodoryApproximation G) D)
  (hPhiLip : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hMorera : forall (phi psi : Nat -> Nat) (f : Complex -> Complex), StrictMono phi -> StrictMono psi -> TendstoLocallyUniformlyOn (fun n => BoundaryRadialTensorTentGeometry.interpolant fkIsingExpandingBoundarySquareCaratheodoryApproximation G (phi (psi n))) f atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U -> Complex.IsConservativeOn f fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hroot : Tendsto (fun n => BoundaryRadialTensorTentGeometry.interpolant fkIsingExpandingBoundarySquareCaratheodoryApproximation G n fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root))) :
-- imply
  TendstoLocallyUniformlyOn (BoundaryRadialTensorTentGeometry.interpolant fkIsingExpandingBoundarySquareCaratheodoryApproximation G) target atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.BoundaryRadialTensorTentGeometry.scalingLimit_of_compactHolder_denseIncidencePaths G Hholder B hanchorBound target Phi D P Hrobin lipschitzConstant hPhiLip htarget htarget_ne hPhi hPhideriv E hMorera hroot


-- created on 2026-10-23
