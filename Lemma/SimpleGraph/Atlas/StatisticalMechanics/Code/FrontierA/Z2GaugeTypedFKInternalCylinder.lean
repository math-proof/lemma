import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKInternalCylinder.Part5
open StatMech StatMech.FrontierA


/--
[mem_cubicalInternalCentralSheet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean)
-/
@[path]
private lemma mem_cubicalInternalCentralSheet_iff_eq
  {N m : Nat}
  {i j : Fin (oddCubeSide m)}
  {f : Fin (oddCubeSide m + 1)}
-- given
  (hNm : N <= m) :
-- imply
  CubicalPlaquette.xy i j f ∈ cubicalInternalCentralSheet N m hNm ↔ m <= i.val ∧ i.val < m + N ∧ m <= j.val ∧ j.val < m + N ∧ f.val = m := by
-- proof
  apply StatMech.FrontierA.mem_cubicalInternalCentralSheet_iff N m hNm i j f

/--
[cubicalInternalCentralSheet_subset_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean)
-/
@[path]
private lemma cubicalInternalCentralSheet_subset_cut_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N <= m) :
-- imply
  cubicalInternalCentralSheet N m hNm ⊆ multibondCut (cubicalDualEnds (a := oddCubeSide m) (b := oddCubeSide m) (c := oddCubeSide m)) (cubicalInternalCentralBlockSpin N m) := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralSheet_subset_cut N m hN hNm

/--
[internalCentralCut_eq_sheet_union_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean)
-/
@[path]
private lemma internalCentralCut_eq_sheet_union_complement_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N <= m) :
-- imply
  multibondCut cubicalDualEnds (cubicalInternalCentralBlockSpin N m) = cubicalInternalCentralSheet N m hNm ∪ cubicalInternalCentralComplement N m hNm := by
-- proof
  apply StatMech.FrontierA.internalCentralCut_eq_sheet_union_complement N m hN hNm

/--
[internalCentralCut_eq_sheet_symmDiff_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean)
-/
@[path]
private lemma internalCentralCut_eq_sheet_symmDiff_complement_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N <= m) :
-- imply
  multibondCut cubicalDualEnds (cubicalInternalCentralBlockSpin N m) = cubicalInternalCentralSheet N m hNm ∆ cubicalInternalCentralComplement N m hNm := by
-- proof
  apply StatMech.FrontierA.internalCentralCut_eq_sheet_symmDiff_complement N m hN hNm

/--
[cubicalInternalCentralUpperVertices_eq_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean)
-/
@[path]
private lemma cubicalInternalCentralUpperVertices_eq_coordinate_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N <= m) :
-- imply
  cubicalInternalCentralUpperVertices N m hNm = cubicalInternalCentralUpperCoordinateVertices N m hNm := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralUpperVertices_eq_coordinate N m hN hNm

/--
[cubicalInternalCentralInnerVertices_subset_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean)
-/
@[path]
private lemma cubicalInternalCentralInnerVertices_subset_boundary_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N < m) :
-- imply
  cubicalInternalCentralInnerVertices N m hNm.le ⊆ cubicalInternalCentralBoundaryVertices N m := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralInnerVertices_subset_boundary N m hN hNm

/--
[cubicalInternalCentralDisconnections_subset_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean)
-/
@[path]
private lemma cubicalInternalCentralDisconnections_subset_consistency_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N <= m) :
-- imply
  finiteEventInter ((cubicalInternalCentralInnerVertices N m hNm).product (cubicalInternalCentralUpperVertices N m hNm)) (fun uv => typedFKDisconnEvent cubicalDualEnds uv.1 uv.2) ⊆ typedFKConsistencyEvent cubicalDualEnds (cubicalInternalCentralSheet N m hNm) := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralDisconnections_subset_consistency N m hN hNm

/--
[cubicalInternalCentral_consistencyMass_ge_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean)
-/
@[path]
private lemma cubicalInternalCentral_consistencyMass_ge_product_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N <= m)
  (J : CubicalPlaquette (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) -> Real)
  (hJ : forall p, 0 <= J p) :
-- imply
  (∏ uv ∈ (cubicalInternalCentralInnerVertices N m hNm).product (cubicalInternalCentralUpperVertices N m hNm), (1 - multibondIsingTwoPoint cubicalDualEnds J uv.1 uv.2)) <= multibondIsingPartition cubicalDualEnds (multibondTwistCoupling J (cubicalInternalCentralSheet N m hNm)) / multibondIsingPartition cubicalDualEnds J := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentral_consistencyMass_ge_product N m hN hNm J hJ

/--
[cubicalInternalCentralWilsonExpectation_ge_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean)
-/
@[path]
private lemma cubicalInternalCentralWilsonExpectation_ge_product_eq
  {N m : Nat}
-- given
  (hN : 0 < N)
  (hNm : N <= m)
  (K : CubicalPlaquette (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) -> Real)
  (hK : forall p, 0 < K p) :
-- imply
  (∏ uv ∈ (cubicalInternalCentralInnerVertices N m hNm).product (cubicalInternalCentralUpperVertices N m hNm), (1 - multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <= gaugeWilsonExpectation cubicalPlaquetteIncidence K (gaugeSurfaceBoundary cubicalPlaquetteIncidence (cubicalInternalCentralSheet N m hNm)) := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralWilsonExpectation_ge_product N m hN hNm K hK


-- created on 2026-10-23
