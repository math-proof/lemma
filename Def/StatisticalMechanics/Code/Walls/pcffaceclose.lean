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
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


def pcf_faceCutGraph (T : Site 2 → Prop) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ (T f ↔ ¬ T g)
  symm := by
    constructor
    intro f g ⟨hadj, hsplit⟩
    refine ⟨hadj.symm, ?_⟩
    by_cases hf : T f <;> by_cases hg : T g <;> simp_all
  loopless := by
    refine ⟨fun f h => ?_⟩
    exact (hypercubicLattice 2).irrefl h.1

end Walls
end StatMech
