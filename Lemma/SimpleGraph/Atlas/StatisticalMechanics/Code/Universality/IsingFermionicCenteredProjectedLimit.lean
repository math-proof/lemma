import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredProjectedLimit
open Filter Metric Set Topology StatMech StatMech.Universality


/--
[tendsto_apply_of_tendstoLocallyUniformlyOn_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredProjectedLimit.lean)
-/
@[path]
private lemma tendsto_apply_of_tendstoLocallyUniformlyOn_of_tendsto_eq
  {F : Nat -> Complex -> Complex}
  {f : Complex -> Complex}
  {x : Nat -> Complex}
  {z : Complex}
-- given
  (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ)
  (hf : ContinuousAt f z)
  (hx : Tendsto x atTop (nhds z)) :
-- imply
  Tendsto (fun n => F n (x n)) atTop (nhds (f z)) := by
-- proof
  apply StatMech.Universality.tendsto_apply_of_tendstoLocallyUniformlyOn_of_tendsto hlimit hf hx

/--
[tendsto_of_dist_tendsto_zero_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredProjectedLimit.lean)
-/
@[path]
private lemma tendsto_of_dist_tendsto_zero_of_tendsto_eq
  [PseudoMetricSpace Y]
  {l : Filter X}
  {f g : X -> Y}
  {y : Y}
-- given
  (hfg : Tendsto (fun x => dist (f x) (g x)) l (nhds 0))
  (hg : Tendsto g l (nhds y)) :
-- imply
  Tendsto f l (nhds y) := by
-- proof
  apply StatMech.Universality.tendsto_of_dist_tendsto_zero_of_tendsto hfg hg

/--
[fkIsingExpandingBoundarySquareCenteredFullObservable_tendsto_of_locallyUniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredProjectedLimit.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredFullObservable_tendsto_of_locallyUniform_eq
  {z : Complex}
-- given
  (target : Complex -> Complex)
  (hlimit : TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop Set.univ)
  (htarget : Continuous target)
  (i j : ∀ k, Fin (2 * fkIsingExpandingSquareSide k))
  (hposition : Tendsto (fun k => (starRingEnd Complex) (isingCenteredRadialGridPosition (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) (i k).1 (j k).1)) atTop (nhds z)) :
-- imply
  Tendsto (fun k => fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) (i k) (j k) / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) atTop (nhds (target z)) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredFullObservable_tendsto_of_locallyUniform target hlimit htarget i j z hposition

/--
[fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_locallyUniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredProjectedLimit.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_locallyUniform_eq
  {side : FKIsingMedialSide}
  {z : Complex}
-- given
  (target : Complex -> Complex)
  (hlimit : TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop Set.univ)
  (htarget : Continuous target)
  (i j : ∀ k, Fin (2 * fkIsingExpandingSquareSide k))
  (hposition : Tendsto (fun k => (starRingEnd Complex) (isingCenteredRadialGridPosition (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) (i k).1 (j k).1)) atTop (nhds z))
  (hinterior : ∀ k, (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k)).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset (fkIsingExpandingSquareSide k)) :
-- imply
  Tendsto (fun k => dist ((fkIsingSquareBoundaryRestrictedDobrushinDomain (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable (fkIsingExpandingSquareMesh k) (.dart (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k), side))) (isingProj (fkIsingSquareWiredDirectedTangent (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) (.dart (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k), side))) (target z))) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_locallyUniform target hlimit htarget i j side z hposition hinterior

/--
[fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_tangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredProjectedLimit.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_tangent_eq
  {side : FKIsingMedialSide}
  {z u : Complex}
-- given
  (target : Complex -> Complex)
  (hlimit : TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCenteredReflectedInterpolant target atTop Set.univ)
  (htarget : Continuous target)
  (i j : ∀ k, Fin (2 * fkIsingExpandingSquareSide k))
  (hposition : Tendsto (fun k => (starRingEnd Complex) (isingCenteredRadialGridPosition (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) (i k).1 (j k).1)) atTop (nhds z))
  (hinterior : ∀ k, (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k)).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset (fkIsingExpandingSquareSide k))
  (htangent : Tendsto (fun k => fkIsingSquareWiredDirectedTangent (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) (.dart (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k), side))) atTop (nhds u)) :
-- imply
  Tendsto (fun k => (fkIsingSquareBoundaryRestrictedDobrushinDomain (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable (fkIsingExpandingSquareMesh k) (.dart (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k), side))) atTop (nhds (isingProj u (target z))) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_tangent target hlimit htarget i j side z u hposition hinterior htangent

/--
[fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_canonicalRationalPaths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredProjectedLimit.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_canonicalRationalPaths_eq
  {bulkRate layerRate : Nat -> Real}
  {L : FKIsingCanonicalDensePrimitiveLocalInputs fkIsingExpandingBoundarySquareCenteredReflectedInterpolant}
  {Hrobin : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs fkIsingExpandingSquareSide fkIsingExpandingSquareSide_pos Phi fkIsingExpandingSquareScale bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
  {i j : forall k, Fin (2 * fkIsingExpandingSquareSide k)}
  {side : FKIsingMedialSide}
  {z : Complex}
-- given
  (target Phi : Complex -> Complex)
  (hPhiLip : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hbase : Tendsto (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) atTop (nhds (target 0)))
  (hposition : Tendsto (fun k => (starRingEnd Complex) (isingCenteredRadialGridPosition (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) (i k).1 (j k).1)) atTop (nhds z))
  (hinterior : forall k, (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k)).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset (fkIsingExpandingSquareSide k)) :
-- imply
  Tendsto (fun k => dist ((fkIsingSquareBoundaryRestrictedDobrushinDomain (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable (fkIsingExpandingSquareMesh k) (.dart (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k), side))) (isingProj (fkIsingSquareWiredDirectedTangent (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) (.dart (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k), side))) (target z))) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_canonicalRationalPaths target Phi L Hrobin lipschitzConstant hPhiLip htarget htarget_ne hPhi hPhideriv E hbase i j side z hposition hinterior

/--
[fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_canonicalRationalPaths_of_tangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredProjectedLimit.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_canonicalRationalPaths_of_tangent_eq
  {bulkRate layerRate : Nat -> Real}
  {L : FKIsingCanonicalDensePrimitiveLocalInputs fkIsingExpandingBoundarySquareCenteredReflectedInterpolant}
  {Hrobin : FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalSplitRobinConsistencyInputs fkIsingExpandingSquareSide fkIsingExpandingSquareSide_pos Phi fkIsingExpandingSquareScale bulkRate layerRate}
  {lipschitzConstant : NNReal}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
  {i j : forall k, Fin (2 * fkIsingExpandingSquareSide k)}
  {side : FKIsingMedialSide}
  {z u : Complex}
-- given
  (target Phi : Complex -> Complex)
  (hPhiLip : LipschitzWith lipschitzConstant (fun z => (Phi z).im))
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hbase : Tendsto (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) atTop (nhds (target 0)))
  (hposition : Tendsto (fun k => (starRingEnd Complex) (isingCenteredRadialGridPosition (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) (i k).1 (j k).1)) atTop (nhds z))
  (hinterior : forall k, (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k)).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset (fkIsingExpandingSquareSide k))
  (htangent : Tendsto (fun k => fkIsingSquareWiredDirectedTangent (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) (.dart (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k), side))) atTop (nhds u)) :
-- imply
  Tendsto (fun k => (fkIsingSquareBoundaryRestrictedDobrushinDomain (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)).normalizedFermionicObservable (fkIsingExpandingSquareMesh k) (.dart (fkIsingSquareCenteredRadialPatchEdge (fkIsingExpandingSquareSide k) (i k) (j k), side))) atTop (nhds (isingProj u (target z))) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredProjectedObservable_tendsto_of_canonicalRationalPaths_of_tangent target Phi L Hrobin lipschitzConstant hPhiLip htarget htarget_ne hPhi hPhideriv E hbase i j side z u hposition hinterior htangent


-- created on 2026-10-23
