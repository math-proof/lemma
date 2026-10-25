/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part3
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

theorem Separates.mono {C C' : Set (Site 2)} (hCC' : C ⊆ C') {n N : ℕ}
    (h : Separates C n N) : Separates C' n N := by
  intro u v hu hv p
  obtain ⟨z, hz, hzC⟩ := h u v hu hv p
  exact ⟨z, hz, hCC' hzC⟩


end BeffaraDC
end StatMech
