/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part2
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


@[simp] theorem mem_contactForceSet {x y z : Site d} :
    z ∈ contactForceSet x y ↔ z ∈ coordinateBetween x y ∧ z ≠ y := by
  classical
  simp only [contactForceSet, Set.Finite.mem_toFinset, Finset.mem_erase]
  tauto


theorem connected_siteToBond_of_contactForceSet
    (eta : ConfigSpace (Site d)) (x y : Site d)
    (hy : eta y = true)
    (hforce : ∀ z ∈ contactForceSet x y, eta z = true) :
    Connected d (siteToBond eta) x y := by
  apply connected_siteToBond_of_coordinateBetween eta x y
  intro z hz
  by_cases hzy : z = y
  · simpa [hzy] using hy
  · exact hforce z (mem_contactForceSet.mpr ⟨hz, hzy⟩)


end StatMech.FrontierA
