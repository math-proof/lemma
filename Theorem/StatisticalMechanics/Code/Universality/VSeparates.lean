/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Def.StatisticalMechanics.Code.Universality.VSeparates
open Set SimpleGraph


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box


theorem liftWalk_support_mem (ω : ConfigSpace (Sym2 (Site 2))) (R : Set (Site 2))
    {x y : R} (w : (openSubgraphInduce 2 ω R).Walk x y) {z : Site 2}
    (hz : z ∈ (liftWalk ω R w).support) :
    ∃ (z' : R), z' ∈ w.support ∧ (z' : Site 2) = z := by
  have hsupp := SimpleGraph.Walk.support_map (projHom ω R) w
  obtain ⟨z', hz'_mem, hz'_eq⟩ := (List.mem_map).mp (hsupp ▸ hz)
  exact ⟨z', hz'_mem, hz'_eq⟩


end Universality
end StatMech
