/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
import Def.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

@[simp] theorem pmd_boxFaceBarrier_adj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (f g : Site 2) :
    (pmd_boxFaceBarrier ω n).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧
        ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧
          bdEdge (bcd_leftReach ω n) s(p, q) ∧ p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n := Iff.rfl


theorem pmd_boxFaceBarrier_le_faceOpenDual (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    pmd_boxFaceBarrier ω n ≤ fci_faceOpenDual ω := by
  rintro f g ⟨hadj, p, q, hpq, hbd, hp, hq⟩
  refine ⟨hadj, ?_⟩
  have hpadj : (hypercubicLattice 2).Adj p q := by
    obtain ⟨p', q', hpq', hadj'⟩ := sharedPrimalEdge_isLatticeEdge hadj
    rw [hpq'] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2
    · exact hadj'
    · exact hadj'.symm
  rw [bdEdge_mk] at hbd
  rw [hpq]
  by_cases hpL : p ∈ bcd_leftReach ω n
  · exact bcd_leftReach_boundary_closed ω n hpL hq hpadj (hbd.mp hpL)
  · have hqL : q ∈ bcd_leftReach ω n := by by_contra hqn; exact hpL (hbd.mpr hqn)
    rw [Sym2.eq_swap]
    exact bcd_leftReach_boundary_closed ω n hqL hp hpadj.symm hpL


end Universality
end StatMech
