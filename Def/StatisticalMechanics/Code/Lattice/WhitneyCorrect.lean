/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable def whc_dualCross (H : SimpleGraph (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ := by
  classical
  exact w.edges.countP (fun e => decide (Sym2.lift ⟨fun a b =>
      sharedPrimalEdge a b ∈ H.edgeSet ∨ sharedPrimalEdge b a ∈ H.edgeSet, by
    intro a b; simp only [eq_iff_iff]; tauto⟩ e))


def whc_isCross (H : SimpleGraph (Site 2)) (a b : Site 2) : Prop :=
  sharedPrimalEdge a b ∈ H.edgeSet ∨ sharedPrimalEdge b a ∈ H.edgeSet

end Lattice
end StatMech
