/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Def.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration.Part4


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


theorem hexSmallCell_hgeom (a : ℂ) (h0 : ℤ) (v : Fin 1) (j : Fin 3) :
    (hexUncondDomain a h0).mid v j - (hexUncondDomain a h0).pos v =
      (1 / 2 : ℂ) * hexUnit (hexSmallCellHeading h0 j) := by
  fin_cases j
  · change hexConcreteV a h0 + hexConcreteDu a h0 - hexConcreteV a h0 =
      (1 / 2 : ℂ) * hexUnit (h0 + 3 + 2 * (0 : ℤ))
    unfold hexConcreteDu halfStep
    rw [show h0 + 3 + 2 * (0 : ℤ) = h0 + 3 by ring,
      hexUnit_add_three]
    ring
  · change hexConcreteV a h0 + hexOmega * hexConcreteDu a h0 -
        hexConcreteV a h0 =
      (1 / 2 : ℂ) * hexUnit (h0 + 3 + 2 * (1 : ℤ))
    unfold hexConcreteDu halfStep
    rw [show h0 + 3 + 2 * (1 : ℤ) = (h0 + 3) + 2 by ring,
      hexFam_hexUnit_add_two, hexUnit_add_three]
    ring
  · change hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0 -
        hexConcreteV a h0 =
      (1 / 2 : ℂ) * hexUnit (h0 + 3 + 2 * (2 : ℤ))
    unfold hexConcreteDu halfStep
    rw [show h0 + 3 + 2 * (2 : ℤ) = (h0 + 3) + 4 by ring,
      hexUnit_add_four, hexUnit_add_three]
    ring


end StatMech.Universality
