/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pcffaceclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Walls.pcffaceclose
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


noncomputable instance pcf_instLocallyFinite (T : Site 2 → Prop) :
    SimpleGraph.LocallyFinite (pcf_faceCutGraph T) := by
  classical
  exact fun f =>
    Fintype.ofFinset
      ((candFinset 2 f).filter (fun g => (pcf_faceCutGraph T).Adj f g)) (by
        intro g
        rw [Finset.mem_filter, SimpleGraph.mem_neighborSet]
        refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
        exact mem_candFinset_of_adj 2 f g (pcf_faceCutGraph_le T h))


end Walls
end StatMech
