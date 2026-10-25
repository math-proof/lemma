/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Lattice.BoundaryConditions
open scoped BigOperators


set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem isOpen_symm {ω : Sym2 V → Bool} {x y : V} (h : IsOpen G ω x y) :
    IsOpen G ω y x := by
  obtain ⟨hadj, hopen⟩ := h
  refine ⟨hadj.symm, ?_⟩
  rwa [Sym2.eq_swap]

theorem isOpen_irrefl {ω : Sym2 V → Bool} (x : V) : ¬ IsOpen G ω x x :=
  fun h => h.1.ne rfl

end Lattice
end StatMech
