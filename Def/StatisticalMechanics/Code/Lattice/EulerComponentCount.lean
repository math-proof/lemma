/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount
open SimpleGraph Set


set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


def ecc_DualCutModel (A : SimpleGraph V) (B' : Set (Sym2 V)) (a b : V) : Prop :=
  (A.deleteEdges B').Connected ∧
    s(a, b) ∈ (A.deleteEdges B').edgeSet ∧
    ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b


end Lattice
end StatMech
