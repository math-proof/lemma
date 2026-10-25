/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

def jce_HorizStepResidue : Prop :=
  ∀ (E : Finset (Sym2 (Site 2))), jce_ClosedContour (E : Set (Sym2 (Site 2))) →
    ∀ a b : ℤ, (s(![a + 1, b], ![a + 1, b + 1]) ∈ E ↔
      (jce_phi E ![a, b] ↔ ¬ jce_phi E ![a + 1, b]))


open Classical in


noncomputable def jce_Hc (E : Finset (Sym2 (Site 2))) (c b : ℤ) : ℕ :=
  (E.filter (fun e => jce_horizBelow c b e)).card

end Lattice
end StatMech
