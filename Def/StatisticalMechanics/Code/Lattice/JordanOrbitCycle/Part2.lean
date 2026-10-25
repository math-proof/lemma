/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchMatching.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Wall1EmbeddingRetry
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanOrbitCycle
open SimpleGraph Set Function


namespace StatMech

namespace Lattice

def joc_Ltromino : Set (Site 2) := {![0, 0], ![1, 0], ![0, 1]}


end Lattice
end StatMech
