import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry
open StatMech StatMech.FrontierA


/--
[sum_fin_pow_natDist_le_two_finiteGeom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma sum_fin_pow_natDist_le_two_finiteGeom_eq
  {N : Nat}
  {r : Real}
  {i : Fin N}
-- given
  (hr : 0 <= r) :
-- imply
  (∑ j : Fin N, r ^ Nat.dist i.val j.val) <= 2 * finiteGeom r N := by
-- proof
  apply StatMech.FrontierA.sum_fin_pow_natDist_le_two_finiteGeom r hr i

/--
[finiteGeom_le_inv_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma finiteGeom_le_inv_one_sub_eq
  {r : Real}
  {N : Nat}
-- given
  (hr0 : 0 <= r)
  (hr1 : r < 1) :
-- imply
  finiteGeom r N <= (1 - r)⁻¹ := by
-- proof
  apply StatMech.FrontierA.finiteGeom_le_inv_one_sub hr0 hr1 N

/--
[sum_fin_prod_pow_l1_le_four_finiteGeom_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma sum_fin_prod_pow_l1_le_four_finiteGeom_sq_eq
  {N : Nat}
  {r : Real}
  {x y : Fin N}
  {depth : Nat}
-- given
  (hr : 0 <= r) :
-- imply
  (∑ ij : Fin N × Fin N, r ^ (Nat.dist x.val ij.1.val + Nat.dist y.val ij.2.val + depth)) <= 4 * (finiteGeom r N) ^ 2 * r ^ depth := by
-- proof
  apply StatMech.FrontierA.sum_fin_prod_pow_l1_le_four_finiteGeom_sq r hr x y depth

/--
[sum_union_le_add_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma sum_union_le_add_of_nonneg_eq
  [DecidableEq alpha]
  {s t : Finset alpha}
-- given
  (f : alpha -> Real)
  (hf : forall x, 0 <= f x) :
-- imply
  ∑ x ∈ s ∪ t, f x <= (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
-- proof
  apply StatMech.FrontierA.sum_union_le_add_of_nonneg s t f hf

/--
[nat_mul_pow_le_finiteGeom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma nat_mul_pow_le_finiteGeom_eq
  {r : Real}
  {N : Nat}
-- given
  (hr0 : 0 <= r)
  (hr1 : r <= 1) :
-- imply
  (N : Real) * r ^ N <= finiteGeom r N := by
-- proof
  apply StatMech.FrontierA.nat_mul_pow_le_finiteGeom hr0 hr1 N

/--
[sum_fin_pow_reverseDepth_le_finiteGeom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma sum_fin_pow_reverseDepth_le_finiteGeom_eq
  {N : Nat}
  {r : Real}
-- given
  (hr0 : 0 <= r)
  (hr1 : r <= 1) :
-- imply
  (∑ z : Fin N, r ^ (N - z.val)) <= finiteGeom r N := by
-- proof
  apply StatMech.FrontierA.sum_fin_pow_reverseDepth_le_finiteGeom hr0 hr1

/--
[squareLowerCapExpSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma squareLowerCapExpSum_le_eq
  {r : Real}
  {N : Nat}
-- given
  (hr0 : 0 <= r)
  (hr1 : r <= 1) :
-- imply
  squareLowerCapExpSum r N <= 4 * finiteGeom r N ^ 3 * N := by
-- proof
  apply StatMech.FrontierA.squareLowerCapExpSum_le hr0 hr1 N

/--
[squareXSideExpSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma squareXSideExpSum_le_eq
  {N : Nat}
  {r : Real}
  {xBoundary : Fin N}
-- given
  (hr0 : 0 <= r)
  (hr1 : r <= 1) :
-- imply
  squareXSideExpSum r xBoundary <= 4 * finiteGeom r N ^ 3 * N := by
-- proof
  apply StatMech.FrontierA.squareXSideExpSum_le hr0 hr1 xBoundary

/--
[squareYSideExpSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma squareYSideExpSum_le_eq
  {N : Nat}
  {r : Real}
  {yBoundary : Fin N}
-- given
  (hr0 : 0 <= r)
  (hr1 : r <= 1) :
-- imply
  squareYSideExpSum r yBoundary <= 4 * finiteGeom r N ^ 3 * N := by
-- proof
  apply StatMech.FrontierA.squareYSideExpSum_le hr0 hr1 yBoundary

/--
[squareCylinderCoordinateExpSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma squareCylinderCoordinateExpSum_le_eq
  {N : Nat}
  {r : Real}
  {west east south north : Fin N}
-- given
  (hr0 : 0 <= r)
  (hr1 : r <= 1) :
-- imply
  squareLowerCapExpSum r N + squareXSideExpSum r west + squareXSideExpSum r east + squareYSideExpSum r south + squareYSideExpSum r north <= 20 * finiteGeom r N ^ 3 * N := by
-- proof
  apply StatMech.FrontierA.squareCylinderCoordinateExpSum_le hr0 hr1 west east south north

/--
[squareCylinderCoordinateExpSum_le_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma squareCylinderCoordinateExpSum_le_inv_eq
  {N : Nat}
  {r : Real}
  {west east south north : Fin N}
-- given
  (hr0 : 0 <= r)
  (hr1 : r < 1) :
-- imply
  squareLowerCapExpSum r N + squareXSideExpSum r west + squareXSideExpSum r east + squareYSideExpSum r south + squareYSideExpSum r north <= 20 * ((1 - r)⁻¹) ^ 3 * N := by
-- proof
  apply StatMech.FrontierA.squareCylinderCoordinateExpSum_le_inv hr0 hr1 west east south north

/--
[centralLowerZ_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma centralLowerZ_val_eq
  {n : Nat}
  {z : Fin (centralSquareSide n)} :
-- imply
  (centralLowerZ z).val = z.val := by
-- proof
  apply StatMech.FrontierA.centralLowerZ_val z

/--
[centralBottomZ_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma centralBottomZ_val_eq
  {n : Nat} :
-- imply
  (centralBottomZ n).val = 0 := by
-- proof
  apply StatMech.FrontierA.centralBottomZ_val n

/--
[finForward_eq_none_iff'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma finForward_eq_none_iff'_eq
  {m : Nat}
  {f : Fin (m + 1)} :
-- imply
  finForward f = none ↔ f = Fin.last m := by
-- proof
  apply StatMech.FrontierA.finForward_eq_none_iff' f

/--
[cubicalLowerComplementInnerVertices_central_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma cubicalLowerComplementInnerVertices_central_subset_eq
  {n : Nat} :
-- imply
  cubicalLowerComplementInnerVertices (a := centralSquareSide n) (b := centralSquareSide n) (c := centralSquareSide n + centralSquareSide n) (centralSquareSheetHeight n) ⊆ centralLowerBoundaryVertices n := by
-- proof
  apply StatMech.FrontierA.cubicalLowerComplementInnerVertices_central_subset n

/--
[centralUpperZ_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma centralUpperZ_val_eq
  {n : Nat} :
-- imply
  (centralUpperZ n).val = centralSquareSide n := by
-- proof
  apply StatMech.FrontierA.centralUpperZ_val n

/--
[cubicalXYSheetUpperVertices_central_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma cubicalXYSheetUpperVertices_central_eq_eq
  {n : Nat} :
-- imply
  cubicalXYSheetUpperVertices (a := centralSquareSide n) (b := centralSquareSide n) (c := centralSquareSide n + centralSquareSide n) (centralSquareSheetHeight n) = centralUpperLayerVertices n := by
-- proof
  apply StatMech.FrontierA.cubicalXYSheetUpperVertices_central_eq n

/--
[centralLowerBottom_doubleSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma centralLowerBottom_doubleSum_eq_eq
  {r : Real}
  {n : Nat} :
-- imply
  (∑ uv ∈ (centralLowerBottomVertices n).product (centralUpperLayerVertices n), r ^ cubicalDualL1 uv.1 uv.2) = squareLowerCapExpSum r (centralSquareSide n) := by
-- proof
  apply StatMech.FrontierA.centralLowerBottom_doubleSum_eq r n

/--
[centralLowerWest_doubleSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma centralLowerWest_doubleSum_eq_eq
  {r : Real}
  {n : Nat} :
-- imply
  (∑ uv ∈ (centralLowerWestVertices n).product (centralUpperLayerVertices n), r ^ cubicalDualL1 uv.1 uv.2) = squareXSideExpSum r (0 : Fin (centralSquareSide n)) := by
-- proof
  apply StatMech.FrontierA.centralLowerWest_doubleSum_eq r n

/--
[centralLowerEast_doubleSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma centralLowerEast_doubleSum_eq_eq
  {r : Real}
  {n : Nat} :
-- imply
  (∑ uv ∈ (centralLowerEastVertices n).product (centralUpperLayerVertices n), r ^ cubicalDualL1 uv.1 uv.2) = squareXSideExpSum r (Fin.last n) := by
-- proof
  apply StatMech.FrontierA.centralLowerEast_doubleSum_eq r n

/--
[centralLowerSouth_doubleSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma centralLowerSouth_doubleSum_eq_eq
  {r : Real}
  {n : Nat} :
-- imply
  (∑ uv ∈ (centralLowerSouthVertices n).product (centralUpperLayerVertices n), r ^ cubicalDualL1 uv.1 uv.2) = squareYSideExpSum r (0 : Fin (centralSquareSide n)) := by
-- proof
  apply StatMech.FrontierA.centralLowerSouth_doubleSum_eq r n

/--
[centralLowerNorth_doubleSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma centralLowerNorth_doubleSum_eq_eq
  {r : Real}
  {n : Nat} :
-- imply
  (∑ uv ∈ (centralLowerNorthVertices n).product (centralUpperLayerVertices n), r ^ cubicalDualL1 uv.1 uv.2) = squareYSideExpSum r (Fin.last n) := by
-- proof
  apply StatMech.FrontierA.centralLowerNorth_doubleSum_eq r n

/--
[centralLowerBoundary_doubleSum_le_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma centralLowerBoundary_doubleSum_le_coordinate_eq
  {r : Real}
  {n : Nat}
-- given
  (hr : 0 <= r) :
-- imply
  (∑ uv ∈ (centralLowerBoundaryVertices n).product (centralUpperLayerVertices n), r ^ cubicalDualL1 uv.1 uv.2) <= squareLowerCapExpSum r (centralSquareSide n) + squareXSideExpSum r (0 : Fin (centralSquareSide n)) + squareXSideExpSum r (Fin.last n) + squareYSideExpSum r (0 : Fin (centralSquareSide n)) + squareYSideExpSum r (Fin.last n) := by
-- proof
  apply StatMech.FrontierA.centralLowerBoundary_doubleSum_le_coordinate hr n

/--
[cubicalLowerSlab_central_pow_l1_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma cubicalLowerSlab_central_pow_l1_sum_le_eq
  {r : Real}
  {n : Nat}
-- given
  (hr0 : 0 <= r)
  (hr1 : r < 1) :
-- imply
  (∑ uv ∈ (cubicalLowerComplementInnerVertices (a := centralSquareSide n) (b := centralSquareSide n) (c := centralSquareSide n + centralSquareSide n) (centralSquareSheetHeight n)).product (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)), r ^ cubicalDualL1 uv.1 uv.2) <= 20 * ((1 - r)⁻¹) ^ 3 * centralSquareSide n := by
-- proof
  apply StatMech.FrontierA.cubicalLowerSlab_central_pow_l1_sum_le hr0 hr1 n

/--
[exp_neg_mul_natCast_eq_pow_exp_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma exp_neg_mul_natCast_eq_pow_exp_neg_eq
  {decay : Real}
  {d : Nat} :
-- imply
  Real.exp (-decay * (d : Real)) = Real.exp (-decay) ^ d := by
-- proof
  apply StatMech.FrontierA.exp_neg_mul_natCast_eq_pow_exp_neg decay d

/--
[cubicalLowerSlab_central_exp_l1_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma cubicalLowerSlab_central_exp_l1_sum_le_eq
  {decay : Real}
  {n : Nat}
-- given
  (hdecay : 0 < decay) :
-- imply
  (∑ uv ∈ (cubicalLowerComplementInnerVertices (a := centralSquareSide n) (b := centralSquareSide n) (c := centralSquareSide n + centralSquareSide n) (centralSquareSheetHeight n)).product (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)), Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) <= 20 * ((1 - Real.exp (-decay))⁻¹) ^ 3 * centralSquareSide n := by
-- proof
  apply StatMech.FrontierA.cubicalLowerSlab_central_exp_l1_sum_le decay hdecay n

/--
[none_not_mem_centralLowerBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma none_not_mem_centralLowerBoundaryVertices_eq
  {n : Nat} :
-- imply
  (none : CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n)) ∉ centralLowerBoundaryVertices n := by
-- proof
  apply StatMech.FrontierA.none_not_mem_centralLowerBoundaryVertices n

/--
[none_not_mem_centralUpperLayerVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma none_not_mem_centralUpperLayerVertices_eq
  {n : Nat} :
-- imply
  (none : CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n)) ∉ centralUpperLayerVertices n := by
-- proof
  apply StatMech.FrontierA.none_not_mem_centralUpperLayerVertices n

/--
[cubicalLowerSlab_central_l1_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma cubicalLowerSlab_central_l1_pos_eq
  {n : Nat}
  {uv : CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n) × CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n)}
-- given
  (huv : uv ∈ (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product (cubicalXYSheetUpperVertices (centralSquareSheetHeight n))) :
-- imply
  0 < cubicalDualL1 uv.1 uv.2 := by
-- proof
  apply StatMech.FrontierA.cubicalLowerSlab_central_l1_pos n uv huv

/--
[cubicalLowerSlab_central_l1_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma cubicalLowerSlab_central_l1_ge_one_eq
  {n : Nat}
  {uv : CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n) × CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n)}
-- given
  (huv : uv ∈ (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product (cubicalXYSheetUpperVertices (centralSquareSheetHeight n))) :
-- imply
  (1 : Real) <= cubicalDualL1 uv.1 uv.2 := by
-- proof
  apply StatMech.FrontierA.cubicalLowerSlab_central_l1_ge_one n uv huv

/--
[cubicalXYWilson_central_perimeterLower_of_l1_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean)
-/
@[path]
private lemma cubicalXYWilson_central_perimeterLower_of_l1_decay_eq
  {n : Nat}
  {decay : Real}
-- given
  (K : CubicalPlaquette (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n) -> Real)
  (hK : forall p, 0 < K p)
  (hdecay : 0 < decay)
  (hcorr : forall uv, uv ∈ (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)) -> multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <= Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) :
-- imply
  Real.exp (-(gaugePerimeterPenalty (Real.exp (-decay)) * (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) * centralSquareSide n) <= gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop (centralSquareSheetHeight n)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilson_central_perimeterLower_of_l1_decay n K hK decay hdecay hcorr


-- created on 2026-10-23
