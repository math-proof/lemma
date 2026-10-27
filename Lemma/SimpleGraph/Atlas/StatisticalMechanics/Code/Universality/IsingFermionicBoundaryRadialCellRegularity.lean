import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
open StatMech StatMech.Universality


/--
[isingProj_div_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma isingProj_div_real_eq
  {e z : Complex}
  {r : Real} :
-- imply
  isingProj e (z / (r : Complex)) = isingProj e z / (r : Complex) := by
-- proof
  apply StatMech.Universality.isingProj_div_real e z r

/--
[projectionCycle_crossParity_norm_div_sub_div_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma projectionCycle_crossParity_norm_div_sub_div_le_eq
  {north east south west : Complex}
  {r delta : Real}
-- given
  (hNE : isingProj 1 north = isingProj 1 east)
  (hES : isingProj Complex.I east = isingProj Complex.I south)
  (hSW : isingProj (-1) south = isingProj (-1) west)
  (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
  (hNS : ‖north / (r : Complex) - south / (r : Complex)‖ ≤ delta)
  (hEW : ‖east / (r : Complex) - west / (r : Complex)‖ ≤ delta) :
-- imply
  ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧ ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta ∧ ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧ ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta := by
-- proof
  apply StatMech.Universality.projectionCycle_crossParity_norm_div_sub_div_le north east south west r delta hNE hES hSW hWN hNS hEW

/--
[complexBilinearCell_norm_sub_le_of_cycle_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma complexBilinearCell_norm_sub_le_of_cycle_edges_eq
  {a00 a10 a01 a11 : Complex}
  {x x' y y' D : Real}
-- given
  (hx0' : 0 ≤ x')
  (hx1' : x' ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1)
  (h10_11 : ‖a10 - a11‖ ≤ D)
  (h11_01 : ‖a11 - a01‖ ≤ D)
  (h01_00 : ‖a01 - a00‖ ≤ D)
  (h00_10 : ‖a00 - a10‖ ≤ D) :
-- imply
  ‖complexBilinearCell a00 a10 a01 a11 x y - complexBilinearCell a00 a10 a01 a11 x' y'‖ ≤ D * (|x - x'| + |y - y'|) := by
-- proof
  apply StatMech.Universality.complexBilinearCell_norm_sub_le_of_cycle_edges a00 a10 a01 a11 x x' y y' D hx0' hx1' hy0 hy1 h10_11 h11_01 h01_00 h00_10

/--
[finiteRadialGridInterpolant_cellPoint_norm_sub_le_of_cycle_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma finiteRadialGridInterpolant_cellPoint_norm_sub_le_of_cycle_edges_eq
  {m : Nat}
  {mesh : Real}
  {value : Fin m → Fin m → Complex}
  {i j : Nat}
  {x x' y y' D : Real}
-- given
  (hmesh : mesh ≠ 0)
  (hi : i + 1 < m)
  (hj : j + 1 < m)
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hx0' : 0 ≤ x')
  (hx1' : x' ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1)
  (hy0' : 0 ≤ y')
  (hy1' : y' ≤ 1)
  (h10_11 : ‖value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩‖ ≤ D)
  (h11_01 : ‖value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j + 1, by omega⟩‖ ≤ D)
  (h01_00 : ‖value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ - value ⟨i, by omega⟩ ⟨j, by omega⟩‖ ≤ D)
  (h00_10 : ‖value ⟨i, by omega⟩ ⟨j, by omega⟩ - value ⟨i + 1, by omega⟩ ⟨j, by omega⟩‖ ≤ D) :
-- imply
  ‖finiteRadialGridInterpolant m mesh value (isingRadialGridCellPoint mesh i j x y) - finiteRadialGridInterpolant m mesh value (isingRadialGridCellPoint mesh i j x' y')‖ ≤ D * (|x - x'| + |y - y'|) := by
-- proof
  apply StatMech.Universality.finiteRadialGridInterpolant_cellPoint_norm_sub_le_of_cycle_edges mesh hmesh value i j hi hj x x' y y' D hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' h10_11 h11_01 h01_00 h00_10

/--
[cellPoint_norm_sub_sq_le_of_coordinate_l1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma cellPoint_norm_sub_sq_le_of_coordinate_l1_eq
  {F : Complex → Complex}
  {mesh : Real}
  {i j : Nat}
  {x x' y y' D : Real}
-- given
  (hmesh : 0 < mesh)
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hx0' : 0 ≤ x')
  (hx1' : x' ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1)
  (hy0' : 0 ≤ y')
  (hy1' : y' ≤ 1)
  (hD : 0 ≤ D)
  (hbound : ‖F (isingRadialGridCellPoint mesh i j x y) - F (isingRadialGridCellPoint mesh i j x' y')‖ ≤ D * (|x - x'| + |y - y'|)) :
-- imply
  ‖F (isingRadialGridCellPoint mesh i j x y) - F (isingRadialGridCellPoint mesh i j x' y')‖ ^ 2 ≤ 8 * (D ^ 2 / mesh) * dist (isingRadialGridCellPoint mesh i j x y) (isingRadialGridCellPoint mesh i j x' y') := by
-- proof
  apply StatMech.Universality.cellPoint_norm_sub_sq_le_of_coordinate_l1 F mesh hmesh i j x x' y y' D hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' hD hbound

/--
[halfScale_cellHolderCoefficient_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma halfScale_cellHolderCoefficient_eq_eq
  {m : Nat}
-- given
  (hm : 0 < m) :
-- imply
  8 * ((2 * ((1 / (m : Real)) * Real.sqrt (264212480 * (m : Real)))) ^ 2 / (1 / (m : Real))) = (8454799360 : Real) := by
-- proof
  apply StatMech.Universality.halfScale_cellHolderCoefficient_eq m hm

/--
[fkIsingSquareBoundaryRadialPatchFullObservable_even_cell_edges_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservable_even_cell_edges_le_eq
  {n m i j : Nat}
  {r delta : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j))
  (hNS : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex) - fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / (r : Complex)‖ ≤ delta)
  (hEW : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩ / (r : Complex) - fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex)‖ ≤ delta) :
-- imply
  let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩ let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩ let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩ let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧ ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta ∧ ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧ ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservable_even_cell_edges_le n m i j hn hm hi0 hi1 hj0 hj1 heven r delta hNS hEW

/--
[fkIsingSquareBoundaryRadialPatchFullObservable_odd_cell_edges_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservable_odd_cell_edges_le_eq
  {n m i j : Nat}
  {r delta : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (hodd : ¬ Even (i + j))
  (hSN : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / (r : Complex) - fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex)‖ ≤ delta)
  (hWE : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex) - fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩ / (r : Complex)‖ ≤ delta) :
-- imply
  let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩ let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩ let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩ let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧ ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta ∧ ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧ ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservable_odd_cell_edges_le n m i j hn hm hi0 hi1 hj0 hj1 hodd r delta hSN hWE

/--
[fkIsingSquareBoundaryRadialPatchFullObservable_cell_edges_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservable_cell_edges_le_eq
  {n m i j : Nat}
  {r delta : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (hNS : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex) - fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / (r : Complex)‖ ≤ delta)
  (hEW : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩ / (r : Complex) - fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex)‖ ≤ delta) :
-- imply
  let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩ let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩ let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩ let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧ ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta ∧ ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧ ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservable_cell_edges_le n m i j hn hm hi0 hi1 hj0 hj1 r delta hNS hEW

/--
[fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_cell_edges_halfScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_cell_edges_halfScale_eq
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
  let F := fkIsingSquareBoundaryRadialPatchFullObservableWindow n m baseI baseJ R hn hm hfitI hfitJ let normalization := Real.sqrt (2 * (1 / (m : Real))) let delta := (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real)) ‖F (⟨a, by omega⟩, ⟨b - 1, by omega⟩) / normalization - F (⟨a, by omega⟩, ⟨b, by omega⟩) / normalization‖ ≤ 2 * delta ∧ ‖F (⟨a, by omega⟩, ⟨b, by omega⟩) / normalization - F (⟨a - 1, by omega⟩, ⟨b, by omega⟩) / normalization‖ ≤ 2 * delta ∧ ‖F (⟨a - 1, by omega⟩, ⟨b, by omega⟩) / normalization - F (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩) / normalization‖ ≤ 2 * delta ∧ ‖F (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩) / normalization - F (⟨a, by omega⟩, ⟨b - 1, by omega⟩) / normalization‖ ≤ 2 * delta := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_cell_edges_halfScale n m baseI baseJ R rho cutoff hn hm hm2 hcutoff hfitI hfitJ hdeep hmcutoff hmrho a b ha0 haR hb0 hbR hrho hmarginN hmarginE hmarginS hmarginW

/--
[fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_tensorTent_cell_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_tensorTent_cell_norm_sub_le_eq
  {n m baseI baseJ R rho cutoff : Nat}
  {a b : Nat}
  {gridScale : Real}
  {x x' y y' : Real}
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
  (hmarginW : IsingLeapfrogInteriorMargin R rho (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩))
  (hgridScale : gridScale ≠ 0)
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hx0' : 0 ≤ x')
  (hx1' : x' ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1)
  (hy0' : 0 ≤ y')
  (hy1' : y' ≤ 1) :
-- imply
  let I := fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant n m hn hm gridScale (1 / (m : Real)) let i := baseI + a - 1 let j := baseJ + b - 1 let delta := (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real)) ‖I (isingRadialGridCellPoint gridScale i j x y) - I (isingRadialGridCellPoint gridScale i j x' y')‖ ≤ (2 * delta) * (|x - x'| + |y - y'|) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_tensorTent_cell_norm_sub_le n m baseI baseJ R rho cutoff hn hm hm2 hcutoff hfitI hfitJ hdeep hmcutoff hmrho a b ha0 haR hb0 hbR hrho hmarginN hmarginE hmarginS hmarginW gridScale hgridScale x x' y y' hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'

/--
[fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_tensorTent_cell_holderHalf_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialCellRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_tensorTent_cell_holderHalf_sq_eq
  {n m baseI baseJ R rho cutoff : Nat}
  {a b : Nat}
  {x x' y y' : Real}
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
  (hmarginW : IsingLeapfrogInteriorMargin R rho (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩))
  (hx0 : 0 ≤ x)
  (hx1 : x ≤ 1)
  (hx0' : 0 ≤ x')
  (hx1' : x' ≤ 1)
  (hy0 : 0 ≤ y)
  (hy1 : y ≤ 1)
  (hy0' : 0 ≤ y')
  (hy1' : y' ≤ 1) :
-- imply
  let mesh := 1 / (m : Real) let I := fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant n m hn hm mesh mesh let i := baseI + a - 1 let j := baseJ + b - 1 ‖I (isingRadialGridCellPoint mesh i j x y) - I (isingRadialGridCellPoint mesh i j x' y')‖ ^ 2 ≤ 8454799360 * dist (isingRadialGridCellPoint mesh i j x y) (isingRadialGridCellPoint mesh i j x' y') := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_tensorTent_cell_holderHalf_sq n m baseI baseJ R rho cutoff hn hm hm2 hcutoff hfitI hfitJ hdeep hmcutoff hmrho a b ha0 haR hb0 hbR hrho hmarginN hmarginE hmarginS hmarginW x x' y y' hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'


-- created on 2026-10-23
