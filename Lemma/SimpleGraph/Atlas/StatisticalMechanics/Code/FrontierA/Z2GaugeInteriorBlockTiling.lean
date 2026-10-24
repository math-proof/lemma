import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling
open Finset Filter Topology StatMech StatMech.FrontierA


/--
[cubicalInteriorBlockTileLoop_eq_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockTileLoop_eq_boundary_eq
  {L p k : Nat}
  {q : Fin k × Fin k} :
-- imply
  cubicalInteriorBlockTileLoop L p k q = gaugeSurfaceBoundary cubicalPlaquetteIncidence (cubicalInteriorBlockTileSheet L p k q) := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockTileLoop_eq_boundary L p k q

/--
[cubicalInteriorBlockTileSheet_pairwise_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockTileSheet_pairwise_disjoint_eq
  {L p k : Nat}
-- given
  (hL : 0 < L) :
-- imply
  ∀ q : Fin k × Fin k, q ∈ (Finset.univ : Finset (Fin k × Fin k)) -> ∀ r : Fin k × Fin k, r ∈ (Finset.univ : Finset (Fin k × Fin k)) -> q ≠ r -> Disjoint (cubicalInteriorBlockTileSheet L p k q) (cubicalInteriorBlockTileSheet L p k r) := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockTileSheet_pairwise_disjoint L p k hL

/--
[cubicalInteriorBlockCentralLoop_eq_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockCentralLoop_eq_boundary_eq
  {L p k : Nat} :
-- imply
  cubicalInteriorBlockCentralLoop L p k = gaugeSurfaceBoundary cubicalPlaquetteIncidence (cubicalInteriorBlockCentralSheet L p k) := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockCentralLoop_eq_boundary L p k

/--
[cubicalInteriorBlockTileSheet_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockTileSheet_biUnion_eq
  {L p k : Nat}
-- given
  (hL : 0 < L) :
-- imply
  (Finset.univ : Finset (Fin k × Fin k)).biUnion (cubicalInteriorBlockTileSheet L p k) = cubicalInteriorBlockCentralSheet L p k := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockTileSheet_biUnion L p k hL

/--
[cubicalPaddedWilsonExpectation_pow_sq_le_interiorBlockCentral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalPaddedWilsonExpectation_pow_sq_le_interiorBlockCentral_eq
  {K : Real}
  {L p k : Nat}
-- given
  (hK : 0 < K)
  (hL : 0 < L) :
-- imply
  (cubicalPaddedWilsonExpectation K L L p p p p p p) ^ (k * k) <= gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ : CubicalPlaquette (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) => K) (cubicalInteriorBlockCentralLoop L p k) := by
-- proof
  apply StatMech.FrontierA.cubicalPaddedWilsonExpectation_pow_sq_le_interiorBlockCentral hK L p k hL

/--
[cubicalInteriorBlockCentralDisorderFreeEnergy_le_tiles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockCentralDisorderFreeEnergy_le_tiles_eq
  {K : Real}
  {L p k : Nat}
-- given
  (hK : 0 < K)
  (hL : 0 < L)
  (hp : 0 < p)
  (hk : 0 < k) :
-- imply
  multibondDisorderFreeEnergy cubicalDualEnds (fun _ : CubicalPlaquette (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K) (cubicalInteriorBlockCentralSheet L p k) <= (k * k : Nat) * cubicalPaddedDisorderFreeEnergy K L L p p p p p p := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockCentralDisorderFreeEnergy_le_tiles hK L p k hL hp hk

/--
[cubicalInteriorBlockCentralSheet_subset_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockCentralSheet_subset_full_eq
  {L p k : Nat} :
-- imply
  cubicalInteriorBlockCentralSheet L p k ⊆ cubicalInteriorBlockFullSheet L p k := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockCentralSheet_subset_full L p k

/--
[cubicalInteriorBlockFull_symmDiff_central](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockFull_symmDiff_central_eq
  {L p k : Nat} :
-- imply
  cubicalInteriorBlockFullSheet L p k ∆ cubicalInteriorBlockCentralSheet L p k = cubicalInteriorBlockFrame L p k := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockFull_symmDiff_central L p k

/--
[card_cubicalInteriorBlockFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma card_cubicalInteriorBlockFrame_eq
  {L p k : Nat} :
-- imply
  (cubicalInteriorBlockFrame L p k).card = (cubicalInteriorBlockSide L p k) ^ 2 - (k * L) ^ 2 := by
-- proof
  apply StatMech.FrontierA.card_cubicalInteriorBlockFrame L p k

/--
[cubicalInteriorBlockFullDisorderFreeEnergy_le_central_add_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockFullDisorderFreeEnergy_le_central_add_frame_eq
  {K : Real}
  {L p k : Nat}
-- given
  (hK : 0 < K) :
-- imply
  multibondDisorderFreeEnergy cubicalDualEnds (fun _ : CubicalPlaquette (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K) (cubicalInteriorBlockFullSheet L p k) <= multibondDisorderFreeEnergy cubicalDualEnds (fun _ : CubicalPlaquette (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K) (cubicalInteriorBlockCentralSheet L p k) + 2 * (cubicalInteriorBlockFrame L p k).card * gaugeDualCoupling K := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockFullDisorderFreeEnergy_le_central_add_frame hK L p k

/--
[cubicalInteriorBlockBottomSheet_subset_slabComplement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockBottomSheet_subset_slabComplement_eq
  {L p k : Nat}
-- given
  (hp : 0 < p) :
-- imply
  cubicalInteriorBlockBottomSheet L p k ⊆ cubicalInteriorBlockSlabComplement L p k := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockBottomSheet_subset_slabComplement L p k hp

/--
[cubicalInteriorBlockSlabComplement_symmDiff_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockSlabComplement_symmDiff_bottom_eq
  {L p k : Nat}
-- given
  (hp : 0 < p) :
-- imply
  cubicalInteriorBlockSlabComplement L p k ∆ cubicalInteriorBlockBottomSheet L p k = cubicalInteriorBlockSlabSideWall L p k := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockSlabComplement_symmDiff_bottom L p k hp

/--
[cubicalInteriorBlockSlabSideWall_subset_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockSlabSideWall_subset_faces_eq
  {L p k : Nat}
-- given
  (hp : 0 < p) :
-- imply
  cubicalInteriorBlockSlabSideWall L p k ⊆ cubicalInteriorBlockSideWallFaces L p k := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockSlabSideWall_subset_faces L p k hp

/--
[card_cubicalInteriorBlockSideWallFaces_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma card_cubicalInteriorBlockSideWallFaces_le_eq
  {L p k : Nat} :
-- imply
  (cubicalInteriorBlockSideWallFaces L p k).card <= 4 * cubicalInteriorBlockSide L p k * p := by
-- proof
  apply StatMech.FrontierA.card_cubicalInteriorBlockSideWallFaces_le L p k

/--
[card_cubicalInteriorBlockSlabSideWall_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma card_cubicalInteriorBlockSlabSideWall_le_eq
  {L p k : Nat}
-- given
  (hp : 0 < p) :
-- imply
  (cubicalInteriorBlockSlabSideWall L p k).card <= 4 * cubicalInteriorBlockSide L p k * p := by
-- proof
  apply StatMech.FrontierA.card_cubicalInteriorBlockSlabSideWall_le L p k hp

/--
[cubicalInteriorBlockBottomDisorderFreeEnergy_le_full_add_sideWall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalInteriorBlockBottomDisorderFreeEnergy_le_full_add_sideWall_eq
  {K : Real}
  {L p k : Nat}
-- given
  (hK : 0 < K)
  (hp : 0 < p) :
-- imply
  multibondDisorderFreeEnergy cubicalDualEnds (fun _ : CubicalPlaquette (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K) (cubicalInteriorBlockBottomSheet L p k) <= multibondDisorderFreeEnergy cubicalDualEnds (fun _ : CubicalPlaquette (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) => gaugeDualCoupling K) (cubicalInteriorBlockFullSheet L p k) + 2 * (cubicalInteriorBlockSlabSideWall L p k).card * gaugeDualCoupling K := by
-- proof
  apply StatMech.FrontierA.cubicalInteriorBlockBottomDisorderFreeEnergy_le_full_add_sideWall hK L p k hp

/--
[cubicalRectangularWilsonFreeEnergy_interiorBlock_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_interiorBlock_le_eq
  {K : Real}
  {L p k : Nat}
-- given
  (hK : 0 < K)
  (hL : 0 < L)
  (hp : 0 < p)
  (hk : 0 < k) :
-- imply
  cubicalRectangularWilsonFreeEnergy K (cubicalInteriorBlockSide L p k) (cubicalInteriorBlockSide L p k) <= (k * k : Nat) * cubicalPaddedDisorderFreeEnergy K L L p p p p p p + 16 * cubicalInteriorBlockSide L p k * p * gaugeDualCoupling K := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_interiorBlock_le hK L p k hL hp hk

/--
[rectangularIsingSurfaceTension_le_paddedDisorderDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_le_paddedDisorderDensity_eq
  {K : Real}
  {L p : Nat}
-- given
  (hK : 0 < K)
  (hL : 0 < L)
  (hp : 0 < p) :
-- imply
  rectangularIsingSurfaceTension (gaugeDualCoupling K) <= cubicalPaddedDisorderFreeEnergy K L L p p p p p p / (L : Real) ^ 2 := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_le_paddedDisorderDensity hK L p hL hp


-- created on 2026-10-23
