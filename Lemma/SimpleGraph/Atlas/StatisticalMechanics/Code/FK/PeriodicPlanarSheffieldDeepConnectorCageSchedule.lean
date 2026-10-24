import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorCageSchedule
open MeasureTheory Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[SymmetricBandDeepConnectorCageCertificate.disjoint_boundaryBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCageSchedule.lean)
-/
@[path]
private lemma disjoint_boundaryBand_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {B rPrimal Rdeep rDual : Real}
  {band width : Nat}
  {L U : Finset V}
  {cert : SymmetricBandDeepConnectorCageCertificate D B rPrimal Rdeep rDual band width L U}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hvw t - D.primalEmbedding.vertex v) i| ≤ B)
  (hBd : ∀ {v w : W} (hvw : Pdual.graph.Adj v w) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hvw t - D.dualEmbedding.vertex v) i| ≤ B) :
-- imply
  Disjoint (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent rPrimal Rdeep (-(band : Real)) band width L U) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster rDual (-(band : Real)) band) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.SymmetricBandDeepConnectorCageCertificate.disjoint_boundaryBand cert hBpos hBp hBd

/--
[complementaryDual_rightHalfPlane_measure_eq_zero_of_symmetricBandCages](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCageSchedule.lean)
-/
@[path]
private lemma complementaryDual_rightHalfPlane_measure_eq_zero_of_symmetricBandCages_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {rDual : Real}
  {rPrimal Rdeep : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
  (hdualUnique : D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hBpos : 0 < B)
  (hBp : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hvw t - D.primalEmbedding.vertex v) i| ≤ B)
  (hBd : ∀ {v w : W} (hvw : Pdual.graph.Adj v w) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hvw t - D.dualEmbedding.vertex v) i| ≤ B)
  (hrR : rPrimal ≤ Rdeep)
  (hcage : ∀ (band : Nat) (L U : Finset V) (width : Nat), (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices Rdeep → (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices Rdeep → U = L.image (P.shift (verticalShift (1 + 2 * (band : Int)))) → SymmetricBandDeepConnectorCageCertificate D B rPrimal Rdeep rDual band width L U) :
-- imply
  D.dualMeasure mu (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.complementaryDual_rightHalfPlane_measure_eq_zero_of_symmetricBandCages D mu hFKG hTI hunique hdualErgodic hdualUnique hBpos hBp hBd rDual hrR hcage

/--
[freeBufferedInfiniteVolume_complementaryDual_rightHalfPlane_zero_of_symmetricBandCages](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCageSchedule.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_complementaryDual_rightHalfPlane_zero_of_symmetricBandCages_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
  {B : Real}
  {rDual : Real}
  {rPrimal Rdeep : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hcommon : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1)
  (hBpos : 0 < B)
  (hBp : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hvw t - D.primalEmbedding.vertex v) i| ≤ B)
  (hBd : ∀ {v w : W} (hvw : Pdual.graph.Adj v w) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hvw t - D.dualEmbedding.vertex v) i| ≤ B)
  (hrR : rPrimal ≤ Rdeep)
  (hcage : ∀ (band : Nat) (L U : Finset V) (width : Nat), (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices Rdeep → (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices Rdeep → U = L.image (P.shift (verticalShift (1 + 2 * (band : Int)))) → SymmetricBandDeepConnectorCageCertificate D B rPrimal Rdeep rDual band width L U) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) D.dualMeasure mu (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_complementaryDual_rightHalfPlane_zero_of_symmetricBandCages D hp hp1 hq hcommon hBpos hBp hBd rDual hrR hcage


-- created on 2026-10-23
