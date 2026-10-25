/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingConstruct.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part4
open SimpleGraph Set


namespace StatMech

namespace Lattice

def jkr_lineRel (a b : Site 2) : Prop :=
  a 1 = 0 ∧ b 1 = 0 ∧ ¬ ({a 0, b 0} = ({0, 1} : Finset ℤ))


def jkr_lineH : SimpleGraph (Site 2) where
  Adj a b := (hypercubicLattice 2).Adj a b ∧ jkr_lineRel a b
  symm := by
    constructor
    rintro a b ⟨hadj, h0, h1, hne⟩
    refine ⟨hadj.symm, h1, h0, ?_⟩
    rwa [Finset.pair_comm]
  loopless := ⟨fun a h => (hypercubicLattice 2).irrefl h.1⟩

end Lattice
end StatMech
