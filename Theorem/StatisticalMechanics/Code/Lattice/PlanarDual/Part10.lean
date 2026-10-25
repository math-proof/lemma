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
import Def.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
open SimpleGraph


namespace StatMech

namespace Lattice

theorem isOpen_iff_dual_isClosed (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    ω e = true ↔ dualConfig ω (crossEdge e) = false := by
  unfold dualConfig
  rw [Equiv.symm_apply_apply]
  cases ω e <;> simp


theorem dual_isOpen_iff_isClosed (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    dualConfig ω e = true ↔ ω (crossEdge.symm e) = false := by
  unfold dualConfig
  cases ω (crossEdge.symm e) <;> simp


theorem dualConfig_dualConfig (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    dualConfig (dualConfig ω) e = ω (crossEdge.symm (crossEdge.symm e)) := by
  unfold dualConfig
  rw [Bool.not_not]

end Lattice
end StatMech
