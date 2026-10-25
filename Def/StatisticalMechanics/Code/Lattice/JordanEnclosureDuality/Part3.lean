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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable def jed_boxEdges : Finset (Sym2 (Site 2)) :=
  { s(![(-1:ℤ), -2], ![0, -2]), s(![(0:ℤ), -2], ![1, -2]), s(![(1:ℤ), -2], ![2, -2]),
    s(![(-1:ℤ), 1], ![0, 1]), s(![(0:ℤ), 1], ![1, 1]), s(![(1:ℤ), 1], ![2, 1]),
    s(![(-1:ℤ), -2], ![-1, -1]), s(![(-1:ℤ), -1], ![-1, 0]), s(![(-1:ℤ), 0], ![-1, 1]),
    s(![(2:ℤ), -2], ![2, -1]), s(![(2:ℤ), -1], ![2, 0]), s(![(2:ℤ), 0], ![2, 1]) }


noncomputable def jed_boxH : SimpleGraph (Site 2) :=
  jed_primalGraph (jed_boxEdges : Set (Sym2 (Site 2)))


end Lattice
end StatMech
