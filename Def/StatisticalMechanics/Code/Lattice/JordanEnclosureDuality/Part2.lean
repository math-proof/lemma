/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepReconnect.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanFiniteDetour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality
open SimpleGraph Set


namespace StatMech

namespace Lattice

def jed_primalGraph (E : Set (Sym2 (Site 2))) : SimpleGraph (Site 2) where
  Adj u w := (hypercubicLattice 2).Adj u w ∧ s(u, w) ∈ E
  symm := by constructor; rintro u w ⟨h1, h2⟩; exact ⟨h1.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun u h => (hypercubicLattice 2).irrefl h.1⟩

end Lattice
end StatMech
