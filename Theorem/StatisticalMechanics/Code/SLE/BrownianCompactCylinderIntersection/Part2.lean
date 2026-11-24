module
public import Theorem.StatisticalMechanics.Code.SLE.BrownianProjectiveContent
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public import Def.StatisticalMechanics.Code.SLE.BrownianCompactCylinderIntersection
open MeasureTheory Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianCompactCylinderIntersection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.SLE

theorem cylinderPrefixSupport_subset
    (I : Nat -> Finset Real) {k n : Nat} (hkn : k <= n) :
    I k <= cylinderPrefixSupport I n := by
  intro t ht
  rw [cylinderPrefixSupport, Finset.mem_biUnion]
  exact ⟨k, Finset.mem_range.2 (by omega), ht⟩


end StatMech.SLE
