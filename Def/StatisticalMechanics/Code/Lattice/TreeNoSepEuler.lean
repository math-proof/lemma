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
import Theorem.StatisticalMechanics.Code.Lattice.TreeNoSepEuler
open SimpleGraph Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


def tnse_IsNonBridgeEdge (A : SimpleGraph V) (e : Sym2 V) : Prop :=
  ∃ a b : V, e = s(a, b) ∧ s(a, b) ∈ A.edgeSet ∧ (A.deleteEdges {s(a, b)}).Reachable a b


end Lattice
end StatMech
