/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
import Def.StatisticalMechanics.Code.Universality.RSWRayTransport.Part3
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


@[simp] theorem rlc_mem_reflectedPrimalRegion_iff
    (K : Set (Site 2)) (x : Site 2) :
    x ∈ rlc_reflectedPrimalRegion K ↔
      rlc_primalDualReflect.symm x ∈ K := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨rlc_primalDualReflect.symm x, hx, by simp⟩


end Universality
end StatMech
