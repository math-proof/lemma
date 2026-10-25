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
import Def.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part2
open SimpleGraph Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


@[simp] theorem tnse_deleteList_nil (A : SimpleGraph V) : tnse_deleteList A [] = A := rfl

@[simp] theorem tnse_deleteList_cons (A : SimpleGraph V) (e : Sym2 V) (L : List (Sym2 V)) :
    tnse_deleteList A (e :: L) = (tnse_deleteList A L).deleteEdges {e} := rfl


end Lattice
end StatMech
