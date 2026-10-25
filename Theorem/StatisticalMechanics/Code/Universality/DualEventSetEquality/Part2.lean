/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Def.StatisticalMechanics.Code.Universality.DualEventSetEquality
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


@[simp] theorem des_negConfig_apply (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    des_negConfig ω e = !(ω e) := rfl


theorem des_negConfig_open_iff_closed (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    des_negConfig ω e = true ↔ ω e = false := by
  rw [des_negConfig_apply]; cases ω e <;> simp


theorem des_isOpenEdge_dual_iff (ω : ConfigSpace (Sym2 (Site 2))) (p q : Site 2) :
    IsOpenEdge 2 (dualConfig ω) p q ↔
      IsOpenEdge 2 (des_negConfig ω) (rot90Inv p) (rot90Inv q) := by
  unfold IsOpenEdge
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨?_, ?_⟩
    · 
      have := (rot90_adj (rot90Inv p) (rot90Inv q))
      rw [show rot90Fun (rot90Inv p) = p from rot90Equiv.right_inv p,
          show rot90Fun (rot90Inv q) = q from rot90Equiv.right_inv q] at this
      exact this.mp hadj
    · rw [des_negConfig_open_iff_closed]
      rw [dual_isOpen_iff_isClosed] at hopen
      rwa [show (crossEdge.symm s(p, q)) = s(rot90Inv p, rot90Inv q) by
        simp [crossEdge, sym2Congr, Sym2.map_mk]] at hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨?_, ?_⟩
    · have := (rot90_adj (rot90Inv p) (rot90Inv q))
      rw [show rot90Fun (rot90Inv p) = p from rot90Equiv.right_inv p,
          show rot90Fun (rot90Inv q) = q from rot90Equiv.right_inv q] at this
      exact this.mpr hadj
    · rw [des_negConfig_open_iff_closed] at hopen
      rw [dual_isOpen_iff_isClosed]
      rwa [show (crossEdge.symm s(p, q)) = s(rot90Inv p, rot90Inv q) by
        simp [crossEdge, sym2Congr, Sym2.map_mk]]


end Universality
end StatMech
