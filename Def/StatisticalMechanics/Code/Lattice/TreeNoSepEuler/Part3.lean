/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
import Theorem.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part3
open SimpleGraph Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


def tnse_AllNonBridge (A : SimpleGraph V) : List (Sym2 V) → Prop
  | [] => True
  | e :: L => tnse_IsNonBridgeEdge (tnse_deleteList A L) e ∧ tnse_AllNonBridge A L

end Lattice
end StatMech
