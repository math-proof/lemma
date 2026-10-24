import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation
open StatMech StatMech.Universality


/--
[isingLinearTent_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma isingLinearTent_continuous_eq :
-- imply
  Continuous isingLinearTent := by
-- proof
  apply StatMech.Universality.isingLinearTent_continuous

/--
[isingLinearTent_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma isingLinearTent_zero_eq :
-- imply
  isingLinearTent 0 = 1 := by
-- proof
  apply StatMech.Universality.isingLinearTent_zero

/--
[isingLinearTent_natCast_sub_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma isingLinearTent_natCast_sub_eq_zero_eq
  {i j : Nat}
-- given
  (hij : i ≠ j) :
-- imply
  isingLinearTent ((i : Real) - (j : Real)) = 0 := by
-- proof
  apply StatMech.Universality.isingLinearTent_natCast_sub_eq_zero i j hij

/--
[isingLinearTent_eq_one_sub_of_mem_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma isingLinearTent_eq_one_sub_of_mem_unit_eq
  {x : Real}
-- given
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1) :
-- imply
  isingLinearTent x = 1 - x := by
-- proof
  apply StatMech.Universality.isingLinearTent_eq_one_sub_of_mem_unit x hx0 hx1

/--
[isingLinearTent_sub_one_eq_of_mem_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma isingLinearTent_sub_one_eq_of_mem_unit_eq
  {x : Real}
-- given
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1) :
-- imply
  isingLinearTent (x - 1) = x := by
-- proof
  apply StatMech.Universality.isingLinearTent_sub_one_eq_of_mem_unit x hx0 hx1

/--
[isingLinearTent_nat_add_mem_unit_sub_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma isingLinearTent_nat_add_mem_unit_sub_eq_zero_eq
  {i a : Nat}
  {x : Real}
-- given
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hai : a ≠ i)
  (hai1 : a ≠ i + 1) :
-- imply
  isingLinearTent ((i : Real) + x - (a : Real)) = 0 := by
-- proof
  apply StatMech.Universality.isingLinearTent_nat_add_mem_unit_sub_eq_zero i a x hx0 hx1 hai hai1

/--
[finite_sum_isingLinearTent_nat_add_mem_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma finite_sum_isingLinearTent_nat_add_mem_unit_eq
  {m : Nat}
  {i : Nat}
  {x : Real}
  {f : Fin m → Complex}
-- given
  (hi : i + 1 < m)
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1) :
-- imply
  ∑ a : Fin m, ((isingLinearTent ((i : Real) + x - (a.1 : Real)) : Real) : Complex) * f a = (((1 - x : Real) : Complex) * f ⟨i, by omega⟩ + ((x : Real) : Complex) * f ⟨i + 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.finite_sum_isingLinearTent_nat_add_mem_unit i hi x hx0 hx1 f

/--
[isingRadialGridCoordinate_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma isingRadialGridCoordinate_position_eq
  {mesh : Real}
  {i j : Nat}
-- given
  (hmesh : mesh ≠ 0) :
-- imply
  isingRadialGridCoordinate mesh (isingRadialGridPosition mesh i j) = ((i : Real), (j : Real)) := by
-- proof
  apply StatMech.Universality.isingRadialGridCoordinate_position mesh hmesh i j

/--
[isingRadialGridCoordinate_cellPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma isingRadialGridCoordinate_cellPoint_eq
  {mesh : Real}
  {i j : Nat}
  {x y : Real}
-- given
  (hmesh : mesh ≠ 0) :
-- imply
  isingRadialGridCoordinate mesh (isingRadialGridCellPoint mesh i j x y) = ((i : Real) + x, (j : Real) + y) := by
-- proof
  apply StatMech.Universality.isingRadialGridCoordinate_cellPoint mesh hmesh i j x y

/--
[isingRadialGridCellPoint_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma isingRadialGridCellPoint_sub_eq
  {mesh : Real}
  {i j : Nat}
  {x x' y y' : Real} :
-- imply
  isingRadialGridCellPoint mesh i j x y - isingRadialGridCellPoint mesh i j x' y' = (mesh : Complex) * ⟨((x - x') + (y - y')) / 2, ((x - x') - (y - y')) / 2⟩ := by
-- proof
  apply StatMech.Universality.isingRadialGridCellPoint_sub mesh i j x x' y y'

/--
[abs_mesh_mul_cellCoordinate_l1_le_four_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma abs_mesh_mul_cellCoordinate_l1_le_four_dist_eq
  {mesh : Real}
  {i j : Nat}
  {x x' y y' : Real} :
-- imply
  |mesh| * (|x - x'| + |y - y'|) ≤ 4 * dist (isingRadialGridCellPoint mesh i j x y) (isingRadialGridCellPoint mesh i j x' y') := by
-- proof
  apply StatMech.Universality.abs_mesh_mul_cellCoordinate_l1_le_four_dist mesh i j x x' y y'

/--
[complexBilinearCell_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma complexBilinearCell_norm_sub_le_eq
  {a00 a10 a01 a11 : Complex}
  {x x' y y' D : Real}
-- given
  (hx0' : 0 ≤ x')
  (hx1' : x' ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1)
  (hbottom : ‖a10 - a00‖ ≤ D)
  (htop : ‖a11 - a01‖ ≤ D)
  (hleft : ‖a01 - a00‖ ≤ D)
  (hright : ‖a11 - a10‖ ≤ D) :
-- imply
  ‖complexBilinearCell a00 a10 a01 a11 x y - complexBilinearCell a00 a10 a01 a11 x' y'‖ ≤ D * (|x - x'| + |y - y'|) := by
-- proof
  apply StatMech.Universality.complexBilinearCell_norm_sub_le a00 a10 a01 a11 x x' y y' D hx0' hx1' hy0 hy1 hbottom htop hleft hright

/--
[isingRadialGridPosition_eq_scaledCarrierPosition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma isingRadialGridPosition_eq_scaledCarrierPosition_eq
  {n m : Nat}
  {mesh : Real}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  isingRadialGridPosition mesh i.1 j.1 = (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) := by
-- proof
  apply StatMech.Universality.isingRadialGridPosition_eq_scaledCarrierPosition n m hn hm mesh i j s

/--
[finiteRadialGridInterpolant_cellPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma finiteRadialGridInterpolant_cellPoint_eq
  {m : Nat}
  {mesh : Real}
  {value : Fin m → Fin m → Complex}
  {i j : Nat}
  {x y : Real}
-- given
  (hmesh : mesh ≠ 0)
  (hi : i + 1 < m)
  (hj : j + 1 < m)
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1) :
-- imply
  finiteRadialGridInterpolant m mesh value (isingRadialGridCellPoint mesh i j x y) = complexBilinearCell (value ⟨i, by omega⟩ ⟨j, by omega⟩) (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) x y := by
-- proof
  apply StatMech.Universality.finiteRadialGridInterpolant_cellPoint mesh hmesh value i j hi hj x y hx0 hx1 hy0 hy1

/--
[finiteRadialGridInterpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma finiteRadialGridInterpolant_continuous_eq
  {m : Nat}
  {mesh : Real}
  {value : Fin m → Fin m → Complex} :
-- imply
  Continuous (finiteRadialGridInterpolant m mesh value) := by
-- proof
  apply StatMech.Universality.finiteRadialGridInterpolant_continuous m mesh value

/--
[finiteRadialGridInterpolant_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma finiteRadialGridInterpolant_position_eq
  {m : Nat}
  {mesh : Real}
  {value : Fin m → Fin m → Complex}
  {i j : Fin m}
-- given
  (hmesh : mesh ≠ 0) :
-- imply
  finiteRadialGridInterpolant m mesh value (isingRadialGridPosition mesh i.1 j.1) = value i j := by
-- proof
  apply StatMech.Universality.finiteRadialGridInterpolant_position m mesh hmesh value i j

/--
[fkIsingSquareBoundaryRadialPatchInterpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchInterpolant_continuous_eq
  {n m : Nat}
  {mesh : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  Continuous (fkIsingSquareBoundaryRadialPatchInterpolant n m hn hm mesh) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchInterpolant_continuous n m hn hm mesh

/--
[fkIsingSquareBoundaryRadialPatchInterpolant_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchInterpolant_position_eq
  {n m : Nat}
  {mesh : Real}
  {i j : Fin m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmesh : mesh ≠ 0) :
-- imply
  fkIsingSquareBoundaryRadialPatchInterpolant n m hn hm mesh (isingRadialGridPosition mesh i.1 j.1) = fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j / (Real.sqrt (2 * mesh) : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchInterpolant_position n m hn hm mesh hmesh i j

/--
[fkIsingSquareBoundaryRadialPatchInterpolant_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchInterpolant_projection_eq
  {n m : Nat}
  {mesh : Real}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmesh : 0 < mesh) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s))) (fkIsingSquareBoundaryRadialPatchInterpolant n m hn hm mesh (isingRadialGridPosition mesh i.1 j.1)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) / (Real.sqrt (2 * mesh) : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchInterpolant_projection n m hn hm mesh hmesh i j s

/--
[fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_continuous_eq
  {n m : Nat}
  {gridScale normalizationScale : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  Continuous (fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant n m hn hm gridScale normalizationScale) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_continuous n m hn hm gridScale normalizationScale

/--
[fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_position_eq
  {n m : Nat}
  {gridScale normalizationScale : Real}
  {i j : Fin m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hgridScale : gridScale ≠ 0) :
-- imply
  fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant n m hn hm gridScale normalizationScale (isingRadialGridPosition gridScale i.1 j.1) = fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j / (Real.sqrt (2 * normalizationScale) : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_position n m hn hm gridScale normalizationScale hgridScale i j

/--
[fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_projection_eq
  {n m : Nat}
  {gridScale normalizationScale : Real}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hgridScale : 0 < gridScale) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s))) (fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant n m hn hm gridScale normalizationScale (isingRadialGridPosition gridScale i.1 j.1)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) / (Real.sqrt (2 * normalizationScale) : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_projection n m hn hm gridScale normalizationScale hgridScale i j s


-- created on 2026-10-23
