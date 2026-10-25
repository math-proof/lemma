/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
open SimpleGraph Set


namespace StatMech

namespace Lattice

def wcl_SymmFlip (flip : Site 2 → Site 2 → Prop) : Prop :=
  ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ flip b a)


noncomputable def wcl_flipCount (flip : Site 2 → Site 2 → Prop) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ := by
  classical
  exact w.edges.countP (fun e => decide (Sym2.lift ⟨fun a b => flip a b ∨ flip b a, by
    intro a b; simp only [eq_iff_iff]; tauto⟩ e))

end Lattice
end StatMech
