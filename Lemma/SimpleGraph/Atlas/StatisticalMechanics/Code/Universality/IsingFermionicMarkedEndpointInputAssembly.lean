import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerTraceAndRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointInputAssembly.lean)
-/
@[path]
private lemma ofFourthOrderLayerTraceAndRange_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {traceRate : Nat -> Real}
  {Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius}
  {Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius}
  {Htrace : PhysicalEndpointOrdinaryTraceData N Phi mesh radius traceRate}
-- given
  (hvertexRadius : forall k, 0 < radius k)
  (hfaceRadius : forall k, 2 <= radius k)
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
  (hscaledFourth_tendsto : Tendsto (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius traceRate (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * mesh k + (3 * isingFermionicGhostCoefficient) * traceRate k) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerTraceAndRange Hfourth Hlayer Htrace hvertexRadius hfaceRadius hmesh_nonneg hvertexRange hfaceRange hscaledFourth_tendsto hmesh_tendsto


-- created on 2026-10-23
