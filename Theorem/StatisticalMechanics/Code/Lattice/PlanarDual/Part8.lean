/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.PlanarDual.Part8
open SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem sym2Congr_mk {α β : Type*} (e : α ≃ β) (a b : α) :
    sym2Congr e s(a, b) = s(e a, e b) := by simp [sym2Congr, Sym2.map_mk]


end Lattice
end StatMech
