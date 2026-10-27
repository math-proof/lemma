import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part8
open StatMech StatMech.Universality


/--
[lipschitzOnWith_of_open_local_on_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma lipschitzOnWith_of_open_local_on_convex_eq
  {s : Set Complex}
  {C : NNReal}
-- given
  (f : Complex -> Complex)
  (hs : Convex Real s)
  (hlocal : ∀ z ∈ s, ∃ u : Set Complex, IsOpen u ∧ z ∈ u ∧ LipschitzOnWith C f (u ∩ s)) :
-- imply
  LipschitzOnWith C f s := by
-- proof
  apply StatMech.Universality.lipschitzOnWith_of_open_local_on_convex f s C hs hlocal

/--
[complexBilinearCell_right_eq_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma complexBilinearCell_right_eq_left_eq
  {a00 a10 a01 a11 b10 b11 : Complex}
  {y : Real} :
-- imply
  complexBilinearCell a00 a10 a01 a11 1 y = complexBilinearCell a10 b10 a11 b11 0 y := by
-- proof
  apply StatMech.Universality.complexBilinearCell_right_eq_left a00 a10 a01 a11 b10 b11 y

/--
[complexBilinearCell_top_eq_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma complexBilinearCell_top_eq_bottom_eq
  {a00 a10 a01 a11 b01 b11 : Complex}
  {x : Real} :
-- imply
  complexBilinearCell a00 a10 a01 a11 x 1 = complexBilinearCell a01 a11 b01 b11 x 0 := by
-- proof
  apply StatMech.Universality.complexBilinearCell_top_eq_bottom a00 a10 a01 a11 b01 b11 x

/--
[complexBilinearCell_horizontalAdjacent_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma complexBilinearCell_horizontalAdjacent_norm_sub_le_eq
  {a00 a10 a01 a11 b10 b11 : Complex}
  {x x' y y' D : Real}
-- given
  (hx0 : 0 <= x)
  (hx1 : x <= 1)
  (hx0' : 0 <= x')
  (hx1' : x' <= 1)
  (hy0 : 0 <= y)
  (hy1 : y <= 1)
  (hy0' : 0 <= y')
  (hy1' : y' <= 1)
  (haBottom : norm (a10 - a00) <= D)
  (haTop : norm (a11 - a01) <= D)
  (haLeft : norm (a01 - a00) <= D)
  (haRight : norm (a11 - a10) <= D)
  (hbBottom : norm (b10 - a10) <= D)
  (hbTop : norm (b11 - a11) <= D)
  (hbRight : norm (b11 - b10) <= D) :
-- imply
  norm (complexBilinearCell a00 a10 a01 a11 x y - complexBilinearCell a10 b10 a11 b11 x' y') <= D * ((1 - x) + x' + |y - y'|) := by
-- proof
  apply StatMech.Universality.complexBilinearCell_horizontalAdjacent_norm_sub_le a00 a10 a01 a11 b10 b11 x x' y y' D hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' haBottom haTop haLeft haRight hbBottom hbTop hbRight

/--
[complexBilinearCell_verticalAdjacent_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma complexBilinearCell_verticalAdjacent_norm_sub_le_eq
  {a00 a10 a01 a11 b01 b11 : Complex}
  {x x' y y' D : Real}
-- given
  (hx0 : 0 <= x)
  (hx1 : x <= 1)
  (hx0' : 0 <= x')
  (hx1' : x' <= 1)
  (hy0 : 0 <= y)
  (hy1 : y <= 1)
  (hy0' : 0 <= y')
  (hy1' : y' <= 1)
  (haBottom : norm (a10 - a00) <= D)
  (haTop : norm (a11 - a01) <= D)
  (haLeft : norm (a01 - a00) <= D)
  (haRight : norm (a11 - a10) <= D)
  (hbTop : norm (b11 - b01) <= D)
  (hbLeft : norm (b01 - a01) <= D)
  (hbRight : norm (b11 - a11) <= D) :
-- imply
  norm (complexBilinearCell a00 a10 a01 a11 x y - complexBilinearCell a01 a11 b01 b11 x' y') <= D * (|x - x'| + (1 - y) + y') := by
-- proof
  apply StatMech.Universality.complexBilinearCell_verticalAdjacent_norm_sub_le a00 a10 a01 a11 b01 b11 x x' y y' D hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' haBottom haTop haLeft haRight hbTop hbLeft hbRight

/--
[complexBilinearHorizontalStrip_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma complexBilinearHorizontalStrip_norm_sub_le_eq
  {a00 a10 a20 a01 a11 a21 : Complex}
  {x x' y D : Real}
-- given
  (hx0 : 0 <= x)
  (hx2 : x <= 2)
  (hx0' : 0 <= x')
  (hx2' : x' <= 2)
  (hy0 : 0 <= y)
  (hy1 : y <= 1)
  (h00_10 : norm (a10 - a00) <= D)
  (h10_20 : norm (a20 - a10) <= D)
  (h01_11 : norm (a11 - a01) <= D)
  (h11_21 : norm (a21 - a11) <= D)
  (h00_01 : norm (a01 - a00) <= D)
  (h10_11 : norm (a11 - a10) <= D)
  (h20_21 : norm (a21 - a20) <= D) :
-- imply
  norm (complexBilinearHorizontalStrip a00 a10 a20 a01 a11 a21 x y - complexBilinearHorizontalStrip a00 a10 a20 a01 a11 a21 x' y) <= D * := by
-- proof
  apply StatMech.Universality.complexBilinearHorizontalStrip_norm_sub_le a00 a10 a20 a01 a11 a21 x x' y D hx0 hx2 hx0' hx2' hy0 hy1 h00_10 h10_20 h01_11 h11_21 h00_01 h10_11 h20_21

/--
[complexBilinearVerticalStrip_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma complexBilinearVerticalStrip_norm_sub_le_eq
  {a00 a10 a01 a11 a02 a12 : Complex}
  {x y y' D : Real}
-- given
  (hx0 : 0 <= x)
  (hx1 : x <= 1)
  (hy0 : 0 <= y)
  (hy2 : y <= 2)
  (hy0' : 0 <= y')
  (hy2' : y' <= 2)
  (h00_10 : norm (a10 - a00) <= D)
  (h01_11 : norm (a11 - a01) <= D)
  (h02_12 : norm (a12 - a02) <= D)
  (h00_01 : norm (a01 - a00) <= D)
  (h01_02 : norm (a02 - a01) <= D)
  (h10_11 : norm (a11 - a10) <= D)
  (h11_12 : norm (a12 - a11) <= D) :
-- imply
  norm (complexBilinearVerticalStrip a00 a10 a01 a11 a02 a12 x y - complexBilinearVerticalStrip a00 a10 a01 a11 a02 a12 x y') <= D * := by
-- proof
  apply StatMech.Universality.complexBilinearVerticalStrip_norm_sub_le a00 a10 a01 a11 a02 a12 x y y' D hx0 hx1 hy0 hy2 hy0' hy2' h00_10 h01_11 h02_12 h00_01 h01_02 h10_11 h11_12

/--
[complexBilinearTwoByTwo_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma complexBilinearTwoByTwo_norm_sub_le_eq
  {a00 a10 a20 a01 a11 a21 a02 a12 a22 : Complex}
  {x x' y y' D : Real}
-- given
  (hx0 : 0 <= x)
  (hx2 : x <= 2)
  (hx0' : 0 <= x')
  (hx2' : x' <= 2)
  (hy0 : 0 <= y)
  (hy2 : y <= 2)
  (hy0' : 0 <= y')
  (hy2' : y' <= 2)
  (h00_10 : norm (a10 - a00) <= D)
  (h10_20 : norm (a20 - a10) <= D)
  (h01_11 : norm (a11 - a01) <= D)
  (h11_21 : norm (a21 - a11) <= D)
  (h02_12 : norm (a12 - a02) <= D)
  (h12_22 : norm (a22 - a12) <= D)
  (h00_01 : norm (a01 - a00) <= D)
  (h01_02 : norm (a02 - a01) <= D)
  (h10_11 : norm (a11 - a10) <= D)
  (h11_12 : norm (a12 - a11) <= D)
  (h20_21 : norm (a21 - a20) <= D)
  (h21_22 : norm (a22 - a21) <= D) :
-- imply
  norm (complexBilinearTwoByTwo a00 a10 a20 a01 a11 a21 a02 a12 a22 x y - complexBilinearTwoByTwo a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') <= D * (|x - x'| + |y - y'|) := by
-- proof
  apply StatMech.Universality.complexBilinearTwoByTwo_norm_sub_le a00 a10 a20 a01 a11 a21 a02 a12 a22 x x' y y' D hx0 hx2 hx0' hx2' hy0 hy2 hy0' hy2' h00_10 h10_20 h01_11 h11_21 h02_12 h12_22 h00_01 h01_02 h10_11 h11_12 h20_21 h21_22

/--
[finiteCenteredRadialGridInterpolant_horizontalBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_horizontalBoundary_eq
  {n : Nat}
  {mesh : Real}
  {i j : Nat}
  {y : Real}
-- given
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex) :
-- imply
  finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i j 1 y) = finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n (i + 1) j 0 y) := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_horizontalBoundary n mesh value i j y

/--
[finiteCenteredRadialGridInterpolant_verticalBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_verticalBoundary_eq
  {n : Nat}
  {mesh : Real}
  {i j : Nat}
  {x : Real}
-- given
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex) :
-- imply
  finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i j x 1) = finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i (j + 1) x 0) := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_verticalBoundary n mesh value i j x

/--
[isingCenteredRadialGridCellPoint_add_one_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma isingCenteredRadialGridCellPoint_add_one_x_eq
  {mesh : Real}
  {n i j : Nat}
  {x y : Real} :
-- imply
  isingCenteredRadialGridCellPoint mesh n i j (1 + x) y = isingCenteredRadialGridCellPoint mesh n (i + 1) j x y := by
-- proof
  apply StatMech.Universality.isingCenteredRadialGridCellPoint_add_one_x mesh n i j x y

/--
[isingCenteredRadialGridCellPoint_add_one_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma isingCenteredRadialGridCellPoint_add_one_y_eq
  {mesh : Real}
  {n i j : Nat}
  {x y : Real} :
-- imply
  isingCenteredRadialGridCellPoint mesh n i j x (1 + y) = isingCenteredRadialGridCellPoint mesh n i (j + 1) x y := by
-- proof
  apply StatMech.Universality.isingCenteredRadialGridCellPoint_add_one_y mesh n i j x y

/--
[finiteCenteredRadialGridInterpolant_twoByTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_twoByTwo_eq
  {n : Nat}
  {mesh : Real}
  {i j : Nat}
  {x y : Real}
-- given
  (hmesh : mesh ≠ 0)
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
  (hi : i + 2 < 2 * n)
  (hj : j + 2 < 2 * n)
  (hx0 : 0 <= x)
  (hx2 : x <= 2)
  (hy0 : 0 <= y)
  (hy2 : y <= 2) :
-- imply
  finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i j x y) = complexBilinearTwoByTwo (value ⟨i, by omega⟩ ⟨j, by omega⟩) (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩) (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩) (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩) (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩) (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩) x y := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_twoByTwo n mesh hmesh value i j hi hj x y hx0 hx2 hy0 hy2

/--
[finiteCenteredRadialGridInterpolant_twoByTwo_norm_sub_le_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_twoByTwo_norm_sub_le_dist_eq
  {n : Nat}
  {mesh : Real}
  {i j : Nat}
  {x x' y y' L : Real}
-- given
  (hmesh : 0 < mesh)
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
  (hi : i + 2 < 2 * n)
  (hj : j + 2 < 2 * n)
  (hx0 : 0 <= x)
  (hx2 : x <= 2)
  (hx0' : 0 <= x')
  (hx2' : x' <= 2)
  (hy0 : 0 <= y)
  (hy2 : y <= 2)
  (hy0' : 0 <= y')
  (hy2' : y' <= 2)
  (hL : 0 <= L)
  (h00_10 : norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (h10_20 : norm (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (h01_11 : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
  (h11_21 : norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
  (h02_12 : norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 2, by omega⟩) <= mesh * L)
  (h12_22 : norm (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩) <= mesh * L)
  (h00_01 : norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (h01_02 : norm (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
  (h10_11 : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (h11_12 : norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
  (h20_21 : norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 2, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (h21_22 : norm (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L) :
-- imply
  norm (finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i j x y) - finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i j x' y')) <= 4 * L * dist (isingCenteredRadialGridCellPoint mesh n i j x y) (isingCenteredRadialGridCellPoint mesh n i j x' y') := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_twoByTwo_norm_sub_le_dist n mesh hmesh value i j hi hj x x' y y' L hx0 hx2 hx0' hx2' hy0 hy2 hy0' hy2' hL h00_10 h10_20 h01_11 h11_21 h02_12 h12_22 h00_01 h01_02 h10_11 h11_12 h20_21 h21_22

/--
[finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le_eq
  {n : Nat}
  {mesh : Real}
  {i j : Nat}
  {x x' y y' D : Real}
-- given
  (hmesh : mesh ≠ 0)
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
  (hi : i + 2 < 2 * n)
  (hj : j + 1 < 2 * n)
  (hx0 : 0 <= x)
  (hx1 : x <= 1)
  (hx0' : 0 <= x')
  (hx1' : x' <= 1)
  (hy0 : 0 <= y)
  (hy1 : y <= 1)
  (hy0' : 0 <= y')
  (hy1' : y' <= 1)
  (haBottom : norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
  (haTop : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= D)
  (haLeft : norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
  (haRight : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= D)
  (hbBottom : norm (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= D)
  (hbTop : norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= D)
  (hbRight : norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 2, by omega⟩ ⟨j, by omega⟩) <= D) :
-- imply
  norm (finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i j x y) - finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y')) <= D * ((1 - x) + x' + |y - y'|) := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le n mesh hmesh value i j hi hj x x' y y' D hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' haBottom haTop haLeft haRight hbBottom hbTop hbRight

/--
[finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le_eq
  {n : Nat}
  {mesh : Real}
  {i j : Nat}
  {x x' y y' D : Real}
-- given
  (hmesh : mesh ≠ 0)
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
  (hi : i + 1 < 2 * n)
  (hj : j + 2 < 2 * n)
  (hx0 : 0 <= x)
  (hx1 : x <= 1)
  (hx0' : 0 <= x')
  (hx1' : x' <= 1)
  (hy0 : 0 <= y)
  (hy1 : y <= 1)
  (hy0' : 0 <= y')
  (hy1' : y' <= 1)
  (haBottom : norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
  (haTop : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= D)
  (haLeft : norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
  (haRight : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= D)
  (hbTop : norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 2, by omega⟩) <= D)
  (hbLeft : norm (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= D)
  (hbRight : norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= D) :
-- imply
  norm (finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i j x y) - finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y')) <= D * (|x - x'| + (1 - y) + y') := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le n mesh hmesh value i j hi hj x x' y y' D hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' haBottom haTop haLeft haRight hbTop hbLeft hbRight

/--
[finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le_dist_eq
  {n : Nat}
  {mesh : Real}
  {i j : Nat}
  {x x' y y' L : Real}
-- given
  (hmesh : 0 < mesh)
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
  (hi : i + 2 < 2 * n)
  (hj : j + 1 < 2 * n)
  (hx0 : 0 <= x)
  (hx1 : x <= 1)
  (hx0' : 0 <= x')
  (hx1' : x' <= 1)
  (hy0 : 0 <= y)
  (hy1 : y <= 1)
  (hy0' : 0 <= y')
  (hy1' : y' <= 1)
  (hL : 0 <= L)
  (haBottom : norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (haTop : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
  (haLeft : norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (haRight : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (hbBottom : norm (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (hbTop : norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
  (hbRight : norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 2, by omega⟩ ⟨j, by omega⟩) <= mesh * L) :
-- imply
  norm (finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i j x y) - finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y')) <= 4 * L * dist (isingCenteredRadialGridCellPoint mesh n i j x y) (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y') := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le_dist n mesh hmesh value i j hi hj x x' y y' L hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' hL haBottom haTop haLeft haRight hbBottom hbTop hbRight

/--
[finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le_dist_eq
  {n : Nat}
  {mesh : Real}
  {i j : Nat}
  {x x' y y' L : Real}
-- given
  (hmesh : 0 < mesh)
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
  (hi : i + 1 < 2 * n)
  (hj : j + 2 < 2 * n)
  (hx0 : 0 <= x)
  (hx1 : x <= 1)
  (hx0' : 0 <= x')
  (hx1' : x' <= 1)
  (hy0 : 0 <= y)
  (hy1 : y <= 1)
  (hy0' : 0 <= y')
  (hy1' : y' <= 1)
  (hL : 0 <= L)
  (haBottom : norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (haTop : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
  (haLeft : norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (haRight : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
  (hbTop : norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 2, by omega⟩) <= mesh * L)
  (hbLeft : norm (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
  (hbRight : norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L) :
-- imply
  norm (finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i j x y) - finiteCenteredRadialGridInterpolant n mesh value (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y')) <= 4 * L * dist (isingCenteredRadialGridCellPoint mesh n i j x y) (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y') := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le_dist n mesh hmesh value i j hi hj x x' y y' L hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' hL haBottom haTop haLeft haRight hbTop hbLeft hbRight

/--
[isingCenteredRadialGridCoordinate_cellPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma isingCenteredRadialGridCoordinate_cellPoint_eq
  {mesh : Real}
  {n i j : Nat}
  {x y : Real}
-- given
  (hmesh : mesh ≠ 0) :
-- imply
  isingCenteredRadialGridCoordinate mesh n (isingCenteredRadialGridCellPoint mesh n i j x y) = ((i : Real) + x, (j : Real) + y) := by
-- proof
  apply StatMech.Universality.isingCenteredRadialGridCoordinate_cellPoint mesh hmesh n i j x y

/--
[isingCenteredRadialGridCellPoint_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma isingCenteredRadialGridCellPoint_coordinate_eq
  {mesh : Real}
  {n i j : Nat}
  {z : Complex}
-- given
  (hmesh : mesh ≠ 0) :
-- imply
  isingCenteredRadialGridCellPoint mesh n i j ((isingCenteredRadialGridCoordinate mesh n z).1 - i) ((isingCenteredRadialGridCoordinate mesh n z).2 - j) = z := by
-- proof
  apply StatMech.Universality.isingCenteredRadialGridCellPoint_coordinate mesh hmesh n i j z

/--
[exists_twoByTwo_cell_of_centeredCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma exists_twoByTwo_cell_of_centeredCoordinate_eq
  {n : Nat}
  {u : Real}
-- given
  (hlo : 1 < u)
  (hhi : u < (2 * n : Nat) - 2) :
-- imply
  ∃ i : Nat, i + 2 < 2 * n ∧ (i : Real) < u ∧ u < (i : Real) + 2 := by
-- proof
  apply StatMech.Universality.exists_twoByTwo_cell_of_centeredCoordinate n u hlo hhi

/--
[closedBall_subset_finiteCenteredRadialGridStrictInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma closedBall_subset_finiteCenteredRadialGridStrictInterior_eq
  {n : Nat}
  {mesh R : Real}
-- given
  (hmesh : 0 < mesh)
  (hR : 0 <= R)
  (hwide : 2 * R + 4 * mesh <= mesh * n) :
-- imply
  closedBall (0 : Complex) R ⊆ finiteCenteredRadialGridStrictInterior n mesh := by
-- proof
  apply StatMech.Universality.closedBall_subset_finiteCenteredRadialGridStrictInterior n mesh R hmesh hR hwide

/--
[closedBall_subset_finiteCenteredRadialGridDeeperInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma closedBall_subset_finiteCenteredRadialGridDeeperInterior_eq
  {n : Nat}
  {mesh R : Real}
-- given
  (hmesh : 0 < mesh)
  (hR : 0 ≤ R)
  (hwide : 2 * R + 5 * mesh ≤ mesh * n) :
-- imply
  closedBall (0 : Complex) R ⊆ finiteCenteredRadialGridDeeperInterior n mesh := by
-- proof
  apply StatMech.Universality.closedBall_subset_finiteCenteredRadialGridDeeperInterior n mesh R hmesh hR hwide

/--
[finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_neighbor_eq
  {n : Nat}
  {mesh : Real}
  {s : Set Complex}
  {L : NNReal}
-- given
  (hmesh : 0 < mesh)
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
  (hs : Convex Real s)
  (hinside : s ⊆ finiteCenteredRadialGridStrictInterior n mesh)
  (hI : ∀ a b : Nat, ∀ (ha : a + 1 < 2 * n) (hb : b < 2 * n), norm (value ⟨a + 1, ha⟩ ⟨b, hb⟩ - value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real))
  (hJ : ∀ a b : Nat, ∀ (ha : a < 2 * n) (hb : b + 1 < 2 * n), norm (value ⟨a, ha⟩ ⟨b + 1, hb⟩ - value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real)) :
-- imply
  LipschitzOnWith (4 * L) (finiteCenteredRadialGridInterpolant n mesh value) s := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_neighbor n mesh hmesh value s hs L hinside hI hJ

/--
[finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_strictNeighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_strictNeighbor_eq
  {n : Nat}
  {mesh : Real}
  {s : Set Complex}
  {L : NNReal}
-- given
  (hmesh : 0 < mesh)
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
  (hs : Convex Real s)
  (hinside : s ⊆ finiteCenteredRadialGridDeeperInterior n mesh)
  (hI : ∀ a b : Nat, ∀ (ha : a + 1 < 2 * n) (hb : b < 2 * n), a + 2 < 2 * n → b + 1 < 2 * n → norm (value ⟨a + 1, ha⟩ ⟨b, hb⟩ - value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real))
  (hJ : ∀ a b : Nat, ∀ (ha : a < 2 * n) (hb : b + 1 < 2 * n), a + 1 < 2 * n → b + 2 < 2 * n → norm (value ⟨a, ha⟩ ⟨b + 1, hb⟩ - value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real)) :
-- imply
  LipschitzOnWith (4 * L) (finiteCenteredRadialGridInterpolant n mesh value) s := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_strictNeighbor n mesh hmesh value s hs L hinside hI hJ

/--
[isingLinearTent_lipschitzWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma isingLinearTent_lipschitzWith_eq :
-- imply
  LipschitzWith 1 isingLinearTent := by
-- proof
  apply StatMech.Universality.isingLinearTent_lipschitzWith

/--
[finiteRadialGridInterpolant_locallyLipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteRadialGridInterpolant_locallyLipschitz_eq
  {m : Nat}
  {mesh : Real}
-- given
  (value : Fin m -> Fin m -> Complex) :
-- imply
  LocallyLipschitz (finiteRadialGridInterpolant m mesh value) := by
-- proof
  apply StatMech.Universality.finiteRadialGridInterpolant_locallyLipschitz m mesh value

/--
[finiteCenteredRadialGridInterpolant_locallyLipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_locallyLipschitz_eq
  {n : Nat}
  {mesh : Real}
-- given
  (value : Fin (2 * n) -> Fin (2 * n) -> Complex) :
-- imply
  LocallyLipschitz (finiteCenteredRadialGridInterpolant n mesh value) := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_locallyLipschitz n mesh value

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_locallyLipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_locallyLipschitz_eq
  {k : Nat} :
-- imply
  LocallyLipschitz (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_locallyLipschitz k

/--
[exists_lipschitzOnWith_forall_lt_of_locallyLipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma exists_lipschitzOnWith_forall_lt_of_locallyLipschitz_eq
  {K : Set Complex}
  {N : Nat}
-- given
  (F : Nat -> Complex -> Complex)
  (hF : ∀ k, LocallyLipschitz (F k))
  (hK : IsCompact K) :
-- imply
  ∃ C : NNReal, ∀ k < N, LipschitzOnWith C (F k) K := by
-- proof
  apply StatMech.Universality.exists_lipschitzOnWith_forall_lt_of_locallyLipschitz F hF K hK N

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_neighbor_eq
  {k : Nat}
  {R : Real}
  {L : NNReal}
-- given
  (hR : 0 <= R)
  (hwide : 2 * R + 4 * fkIsingExpandingSquareScale k <= fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
  (hI : ∀ a b : Nat, ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k) (hb : b < 2 * fkIsingExpandingSquareSide k), norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <= fkIsingExpandingSquareScale k * (L : Real))
  (hJ : ∀ a b : Nat, ∀ (ha : a < 2 * fkIsingExpandingSquareSide k) (hb : b + 1 < 2 * fkIsingExpandingSquareSide k), norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <= fkIsingExpandingSquareScale k * (L : Real)) :
-- imply
  LipschitzOnWith (4 * L) (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) (closedBall (0 : Complex) R) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_neighbor k R L hR hwide hI hJ

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_strictNeighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_strictNeighbor_eq
  {k : Nat}
  {R : Real}
  {L : NNReal}
-- given
  (hR : 0 <= R)
  (hwide : 2 * R + 5 * fkIsingExpandingSquareScale k <= fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
  (hI : ∀ a b : Nat, ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k) (hb : b < 2 * fkIsingExpandingSquareSide k), a + 2 < 2 * fkIsingExpandingSquareSide k → b + 1 < 2 * fkIsingExpandingSquareSide k → norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <= fkIsingExpandingSquareScale k * (L : Real))
  (hJ : ∀ a b : Nat, ∀ (ha : a < 2 * fkIsingExpandingSquareSide k) (hb : b + 1 < 2 * fkIsingExpandingSquareSide k), a + 1 < 2 * fkIsingExpandingSquareSide k → b + 2 < 2 * fkIsingExpandingSquareSide k → norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <= fkIsingExpandingSquareScale k * (L : Real)) :
-- imply
  LipschitzOnWith (4 * L) (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) (closedBall (0 : Complex) R) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_strictNeighbor k R L hR hwide hI hJ

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_horizontalAdjacent_norm_sub_le_of_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_horizontalAdjacent_norm_sub_le_of_neighbor_eq
  {k i j : Nat}
  {x x' y y' L : Real}
-- given
  (hi : i + 2 < 2 * fkIsingExpandingSquareSide k)
  (hj : j + 1 < 2 * fkIsingExpandingSquareSide k)
  (hx0 : 0 <= x)
  (hx1 : x <= 1)
  (hx0' : 0 <= x')
  (hx1' : x' <= 1)
  (hy0 : 0 <= y)
  (hy1 : y <= 1)
  (hy0' : 0 <= y')
  (hy1' : y' <= 1)
  (hI : forall a b (ha : a + 1 < 2 * fkIsingExpandingSquareSide k) (hb : b < 2 * fkIsingExpandingSquareSide k), norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <= fkIsingExpandingSquareScale k * L)
  (hJ : forall a b (ha : a < 2 * fkIsingExpandingSquareSide k) (hb : b + 1 < 2 * fkIsingExpandingSquareSide k), norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <= fkIsingExpandingSquareScale k * L) :
-- imply
  norm (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k ((starRingEnd Complex) (isingCenteredRadialGridCellPoint (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) i j x y)) - fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k ((starRingEnd Complex) (isingCenteredRadialGridCellPoint (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) (i + 1) j x' y'))) <= (fkIsingExpandingSquareScale k * L) * ((1 - x) + x' + |y - y'|) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_horizontalAdjacent_norm_sub_le_of_neighbor k i j hi hj x x' y y' L hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' hI hJ

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_verticalAdjacent_norm_sub_le_of_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_verticalAdjacent_norm_sub_le_of_neighbor_eq
  {k i j : Nat}
  {x x' y y' L : Real}
-- given
  (hi : i + 1 < 2 * fkIsingExpandingSquareSide k)
  (hj : j + 2 < 2 * fkIsingExpandingSquareSide k)
  (hx0 : 0 <= x)
  (hx1 : x <= 1)
  (hx0' : 0 <= x')
  (hx1' : x' <= 1)
  (hy0 : 0 <= y)
  (hy1 : y <= 1)
  (hy0' : 0 <= y')
  (hy1' : y' <= 1)
  (hI : forall a b (ha : a + 1 < 2 * fkIsingExpandingSquareSide k) (hb : b < 2 * fkIsingExpandingSquareSide k), norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <= fkIsingExpandingSquareScale k * L)
  (hJ : forall a b (ha : a < 2 * fkIsingExpandingSquareSide k) (hb : b + 1 < 2 * fkIsingExpandingSquareSide k), norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <= fkIsingExpandingSquareScale k * L) :
-- imply
  norm (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k ((starRingEnd Complex) (isingCenteredRadialGridCellPoint (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) i j x y)) - fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k ((starRingEnd Complex) (isingCenteredRadialGridCellPoint (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) i (j + 1) x' y'))) <= (fkIsingExpandingSquareScale k * L) * (|x - x'| + (1 - y) + y') := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_verticalAdjacent_norm_sub_le_of_neighbor k i j hi hj x x' y y' L hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' hI hJ

/--
[fkIsingExpandingCenteredNeighborTransport_of_four_sector_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingCenteredNeighborTransport_of_four_sector_bounds_eq
  {L : NNReal}
  {N : Nat}
-- given
  (hI : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ a b, isingCenteredRadialIndexSector (fkIsingExpandingSquareSide k) a b = q → FKIsingExpandingCenteredHorizontalNeighborBound L k a b)
  (hJ : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ a b, isingCenteredRadialIndexSector (fkIsingExpandingSquareSide k) a b = q → FKIsingExpandingCenteredVerticalNeighborBound L k a b) :
-- imply
  FKIsingExpandingCenteredNeighborTransport := by
-- proof
  apply StatMech.Universality.fkIsingExpandingCenteredNeighborTransport_of_four_sector_bounds L N hI hJ

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredNeighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredNeighbor_eq
-- given
  (hneighbor : FKIsingExpandingCenteredNeighborTransport) :
-- imply
  fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder fkIsingExpandingBoundarySquareCenteredReflectedInterpolant := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredNeighbor hneighbor

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredStrictNeighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredStrictNeighbor_eq
-- given
  (hneighbor : FKIsingExpandingCenteredStrictNeighborTransport) :
-- imply
  fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder fkIsingExpandingBoundarySquareCenteredReflectedInterpolant := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredStrictNeighbor hneighbor

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_radialPatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_radialPatch_eq
  {n m a b : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (ha : a < m)
  (hb : b < m) :
-- imply
  fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨n + a, by omega⟩ ⟨n + b, by omega⟩ = fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨a, ha⟩ ⟨b, hb⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_radialPatch n m a b hn hm ha hb

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window_eq
  {n m baseI baseJ R : Nat}
  {p : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m) :
-- imply
  fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨n + (baseI + p.1.1), by have := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window n m baseI baseJ R hn hm hfitI hfitJ p

/--
[fkIsingSquareBoundaryCenteredRadialPatch_add_side_normalizedNeighbor_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatch_add_side_normalizedNeighbor_norm_sub_le_eq
  {n m baseI baseJ R rho : Nat}
  {mesh d H V : Real}
  {r : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hdeep : ∀ q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
  (hV : fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r ≤ V)
  (hd : 0 ≤ d)
  (hH : 0 ≤ H)
  (hradius : d ≤ mesh * (rho : Real))
  (hscale : 1032080 * V ≤ H ^ 2 * d ^ 3)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨n + (baseI + p.1.1), by have := p.1.2; omega⟩ ⟨n + (baseJ + p.2.1), by have := p.2.2; omega⟩ / (Real.sqrt (2 * mesh) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨n + (baseI + p'.1.1), by have := p'.1.2; omega⟩ ⟨n + (baseJ + p'.2.1), by have := p'.2.2; omega⟩ / (Real.sqrt (2 * mesh) : Complex)) ≤ mesh * H := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatch_add_side_normalizedNeighbor_norm_sub_le n m baseI baseJ R rho mesh d H V hn hm hm2 hfitI hfitJ hmesh r hdeep hV hd hH hradius hscale p p' hrho hp hp' hpp'

/--
[fkIsingSquareBoundaryCenteredRadialPatch_add_side_cell_edges_halfScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatch_add_side_cell_edges_halfScale_eq
  {n m baseI baseJ R rho cutoff : Nat}
  {a b : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hcutoff : 0 < cutoff)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hdeep : ∀ q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 cutoff)
  (hmcutoff : m ≤ 2 * cutoff)
  (hmrho : m ≤ 2 * rho)
  (ha0 : 0 < a)
  (haR : a < R)
  (hb0 : 0 < b)
  (hbR : b < R)
  (hrho : 0 < rho)
  (hmarginN : IsingLeapfrogInteriorMargin R rho (⟨a, by omega⟩, ⟨b - 1, by omega⟩))
  (hmarginE : IsingLeapfrogInteriorMargin R rho (⟨a, by omega⟩, ⟨b, by omega⟩))
  (hmarginS : IsingLeapfrogInteriorMargin R rho (⟨a - 1, by omega⟩, ⟨b, by omega⟩))
  (hmarginW : IsingLeapfrogInteriorMargin R rho (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)) :
-- imply
  let F : IsingLeapfrogBox R → Complex := fun p ↦ fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨n + (baseI + p.1.1), by have := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatch_add_side_cell_edges_halfScale n m baseI baseJ R rho cutoff hn hm hm2 hcutoff hfitI hfitJ hdeep hmcutoff hmrho a b ha0 haR hb0 hbR hrho hmarginN hmarginE hmarginS hmarginW

/--
[fkIsingSquareBoundaryCenteredRadialPatch_normalizedNeighbor_norm_sub_le_of_radialWindow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatch_normalizedNeighbor_norm_sub_le_of_radialWindow_eq
  {n m baseI baseJ R rho : Nat}
  {mesh d H V : Real}
  {r : Nat}
  {i j i' j' : Fin (2 * n)}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m <= n)
  (hm2 : 2 <= m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hdeep : forall q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
  (hV : fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r <= V)
  (hd : 0 <= d)
  (hH : 0 <= H)
  (hradius : d <= mesh * (rho : Real))
  (hscale : 1032080 * V <= H ^ 2 * d ^ 3)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p')
  (hfirst : fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j = fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p)
  (hsecond : fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i' j' = fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ p') :
-- imply
  norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j / (Real.sqrt (2 * mesh) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i' j' / (Real.sqrt (2 * mesh) : Complex)) <= mesh * H := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatch_normalizedNeighbor_norm_sub_le_of_radialWindow n m baseI baseJ R rho mesh d H V hn hm hm2 hfitI hfitJ hmesh r hdeep hV hd hH hradius hscale i j i' j' p p' hrho hp hp' hpp' hfirst hsecond


-- created on 2026-10-23
