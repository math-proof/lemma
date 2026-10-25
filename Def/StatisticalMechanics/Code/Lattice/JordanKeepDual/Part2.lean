/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

def jkd_gr9rel (i j : Fin 9) : Bool :=
  let ci := (i : ℕ) % 3; let ri := (i : ℕ) / 3
  let cj := (j : ℕ) % 3; let rj := (j : ℕ) / 3
  (ci == cj && (ri == rj + 1 || rj == ri + 1)) || (ri == rj && (ci == cj + 1 || cj == ci + 1))


def jkd_gr9G : SimpleGraph (Fin 9) where
  Adj i j := jkd_gr9rel i j
  symm := by constructor; intro i j h; revert h; revert i j; decide
  loopless := ⟨by intro i h; revert h; revert i; decide⟩

end Lattice
end StatMech
