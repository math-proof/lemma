/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianCompactCylinderIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianProjectiveContent
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.MetricSpace.Bounded
import Def.StatisticalMechanics.Code.SLE.BrownianCompactCylinderIntersection
open MeasureTheory Set


namespace StatMech.SLE

theorem cylinderPrefixSupport_subset
    (I : Nat -> Finset Real) {k n : Nat} (hkn : k <= n) :
    I k <= cylinderPrefixSupport I n := by
  intro t ht
  rw [cylinderPrefixSupport, Finset.mem_biUnion]
  exact ⟨k, Finset.mem_range.2 (by omega), ht⟩


end StatMech.SLE
