/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CheckIsingFermionicPhysicalDeepEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy

#print axioms
  StatMech.Universality.fkIsingSquareRadialPatchCellPrimalDart_injective
#print axioms
  StatMech.Universality.fkIsingSquareRadialPatchCellDualDart_injective
#print axioms
  StatMech.Universality.fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation_eq_cellDarts
#print axioms
  StatMech.Universality.fkIsingSquareRadialPatch_deepCellDiagonalVariation_sum_le
#print axioms
  StatMech.Universality.fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_le
#print axioms
  StatMech.Universality.fkIsingSquareRadialPatchFullObservableWindow_deep_energy_le
#print axioms
  StatMech.Universality.fkIsingSquareRadialPatchFullObservableWindow_deep_diffusive
