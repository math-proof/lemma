import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part3
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[tendsto_isingFermionicQuadraticLipschitz_mul_polynomialMesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointTraceProjection.lean)
-/
@[path]
private lemma tendsto_isingFermionicQuadraticLipschitz_mul_polynomialMesh_eq
  {C : NNReal} :
-- imply
  Tendsto (fun k => (isingFermionicQuadraticLipschitzConstant C k : Real) * isingFermionicPolynomialMesh k) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_isingFermionicQuadraticLipschitz_mul_polynomialMesh C

/--
[LocalBoundaryTraceProjection.error_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointTraceProjection.lean)
-/
@[path]
private lemma error_le_eq
  {Phi : Complex -> Complex}
  {S : Set Complex}
  {L : NNReal}
  {sample : Complex}
  {value mesh : Real}
  {P : LocalBoundaryTraceProjection Phi S L sample value mesh}
-- given
  (hPhi : LipschitzOnWith L (fun z => (Phi z).im) S) :
-- imply
  |value - (Phi sample).im| <= L * mesh := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.LocalBoundaryTraceProjection.error_le P hPhi

/--
[PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerProjectionAndRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointTraceProjection.lean)
-/
@[path]
private lemma ofFourthOrderLayerProjectionAndRange_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius}
  {Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius}
  {P : PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius}
-- given
  (hvertexRadius : forall k, 0 < radius k)
  (hfaceRadius : forall k, 2 <= radius k)
  (hmesh_nonneg : forall k, 0 <= mesh k)
  (hvertexRange : forall k x, 0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\ (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
  (hfaceRange : forall k c, 0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\ (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
  (hscaledFourth_tendsto : Tendsto (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
  (htrace_tendsto : Tendsto (fun k => (P.lipschitzConstant k : Real) * mesh k) atTop (nhds 0))
  (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
-- imply
  PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius (fun k => (P.lipschitzConstant k : Real) * mesh k) (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12) (fun k => (4 * Hlayer.constant) * mesh k + (3 * isingFermionicGhostCoefficient) * ((P.lipschitzConstant k : Real) * mesh k)) (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerProjectionAndRange Hfourth Hlayer P hvertexRadius hfaceRadius hmesh_nonneg hvertexRange hfaceRange hscaledFourth_tendsto htrace_tendsto hmesh_tendsto


-- created on 2026-10-23
