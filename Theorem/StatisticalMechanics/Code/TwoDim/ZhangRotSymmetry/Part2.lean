/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangClose.Part2
import Theorem.StatisticalMechanics.Code.TwoDim.SelfDualDichotomy
import Def.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality


@[simp] theorem zrs_sideFamily_zero (base : Set (ConfigSpace (Sym2 (Site 2)))) :
    zrs_sideFamily base 0 = base := rfl

@[simp] theorem zrs_sideFamily_one (base : Set (ConfigSpace (Sym2 (Site 2)))) :
    zrs_sideFamily base 1 = zrs_rot (zrs_rot base) := rfl

@[simp] theorem zrs_sideFamily_two (base : Set (ConfigSpace (Sym2 (Site 2)))) :
    zrs_sideFamily base 2 = zrs_rot base := rfl

@[simp] theorem zrs_sideFamily_three (base : Set (ConfigSpace (Sym2 (Site 2)))) :
    zrs_sideFamily base 3 = zrs_rot (zrs_rot (zrs_rot base)) := rfl


theorem zrs_sideFamily_isIncreasing {base : Set (ConfigSpace (Sym2 (Site 2)))}
    (hbase : IsIncreasing base) (i : Fin 4) : IsIncreasing (zrs_sideFamily base i) := by
  fin_cases i
  · exact hbase
  · exact zrs_rotPreimage_isIncreasing (zrs_rotPreimage_isIncreasing hbase)
  · exact zrs_rotPreimage_isIncreasing hbase
  · exact zrs_rotPreimage_isIncreasing
      (zrs_rotPreimage_isIncreasing (zrs_rotPreimage_isIncreasing hbase))


theorem zrs_sideFamily_measurableSet {base : Set (ConfigSpace (Sym2 (Site 2)))}
    (hbase : MeasurableSet base) (i : Fin 4) : MeasurableSet (zrs_sideFamily base i) := by
  fin_cases i
  · exact hbase
  · exact zrs_rotPreimage_measurableSet (zrs_rotPreimage_measurableSet hbase)
  · exact zrs_rotPreimage_measurableSet hbase
  · exact zrs_rotPreimage_measurableSet
      (zrs_rotPreimage_measurableSet (zrs_rotPreimage_measurableSet hbase))


theorem zrs_side_symmetry {base : Set (ConfigSpace (Sym2 (Site 2)))}
    (hbase : MeasurableSet base) (i : Fin 4) :
    halfMeasure.real (zrs_sideFamily base i) = halfMeasure.real (zrs_sideFamily base 0) := by
  have hρ := zrs_rotPreimage_measurableSet hbase
  have hρρ := zrs_rotPreimage_measurableSet hρ
  fin_cases i
  · rfl
  · 
    show halfMeasure.real (zrs_rot (zrs_rot base)) = halfMeasure.real base
    simp only [zrs_rot]
    rw [zrs_rotPreimage_measureReal hρ, zrs_rotPreimage_measureReal hbase]
  · 
    show halfMeasure.real (zrs_rot base) = halfMeasure.real base
    simp only [zrs_rot]
    rw [zrs_rotPreimage_measureReal hbase]
  · 
    show halfMeasure.real (zrs_rot (zrs_rot (zrs_rot base))) = halfMeasure.real base
    simp only [zrs_rot]
    rw [zrs_rotPreimage_measureReal hρρ, zrs_rotPreimage_measureReal hρ,
      zrs_rotPreimage_measureReal hbase]


end TwoDim
end StatMech
