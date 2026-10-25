/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepReconnect.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanFiniteDetour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jed_mem_cutSet_iff (T : Site 2 → Prop) {c d : Site 2}
    (hcd : (hypercubicLattice 2).Adj c d) :
    sharedPrimalEdge c d ∈ jed_cutSet T ↔ (T c ↔ ¬ T d) := by
  constructor
  · rintro ⟨a, b, hab, heq, hsplit⟩
    have hsy : s(c, d) = s(a, b) := (jce_sharedPrimalEdge_inj hcd hab).mpr heq
    rw [Sym2.eq_iff] at hsy
    rcases hsy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hsplit
    · tauto
  · intro h; exact ⟨c, d, hcd, rfl, h⟩


theorem jed_sh_right (x y : ℤ) :
    sharedPrimalEdge ![x, y] ![x, y - 1] = s(![x, y], ![x + 1, y]) := by
  rw [sharedPrimalEdge_bottom]; unfold faceCorner00 faceCorner10; norm_num


theorem jed_sh_left (x y : ℤ) :
    sharedPrimalEdge ![x - 1, y] ![x - 1, y - 1] = s(![x - 1, y], ![x, y]) := by
  rw [sharedPrimalEdge_bottom]; unfold faceCorner00 faceCorner10; rw [show (x - 1) + 1 = x by ring]


theorem jed_sh_up (x y : ℤ) :
    sharedPrimalEdge ![x, y] ![x - 1, y] = s(![x, y], ![x, y + 1]) := by
  rw [sharedPrimalEdge_left]; unfold faceCorner00 faceCorner01; norm_num


theorem jed_sh_down (x y : ℤ) :
    sharedPrimalEdge ![x, y - 1] ![x - 1, y - 1] = s(![x, y - 1], ![x, y]) := by
  rw [sharedPrimalEdge_left]; unfold faceCorner00 faceCorner01; rw [show (y - 1) + 1 = y by ring]


theorem jed_cutSet_even (T : Site 2 → Prop) (v : Site 2) :
    Even (jce_degree (jed_cutSet T) v) := by
  classical
  set x := v 0 with hx
  set y := v 1 with hy
  have hv : v = ![x, y] := by funext i; fin_cases i <;> rfl
  rw [jce_degree, Finset.card_filter, Fin.sum_univ_four]
  simp only [jce_nbr, hv, Matrix.cons_val_zero, Matrix.cons_val_one]
  have m0 : (s(![x, y], ![x + 1, y]) ∈ jed_cutSet T) ↔ (T ![x, y] ↔ ¬ T ![x, y - 1]) := by
    rw [← jed_sh_right x y]; exact jed_mem_cutSet_iff T (latAdj_bottom x y)
  have m1 : (s(![x, y], ![x - 1, y]) ∈ jed_cutSet T) ↔ (T ![x - 1, y] ↔ ¬ T ![x - 1, y - 1]) := by
    rw [show s(![x, y], ![x - 1, y]) = s(![x - 1, y], ![x, y]) from Sym2.eq_swap, ← jed_sh_left x y]
    exact jed_mem_cutSet_iff T (latAdj_bottom (x - 1) y)
  have m2 : (s(![x, y], ![x, y + 1]) ∈ jed_cutSet T) ↔ (T ![x, y] ↔ ¬ T ![x - 1, y]) := by
    rw [← jed_sh_up x y]; exact jed_mem_cutSet_iff T (latAdj_left x y)
  have m3 : (s(![x, y], ![x, y - 1]) ∈ jed_cutSet T) ↔ (T ![x, y - 1] ↔ ¬ T ![x - 1, y - 1]) := by
    rw [show s(![x, y], ![x, y - 1]) = s(![x, y - 1], ![x, y]) from Sym2.eq_swap, ← jed_sh_down x y]
    exact jed_mem_cutSet_iff T (latAdj_left x (y - 1))
  rw [m0, m1, m2, m3, Nat.even_iff]
  by_cases hA : T ![x, y] <;> by_cases hB : T ![x, y - 1] <;> by_cases hC : T ![x - 1, y - 1] <;>
    by_cases hD : T ![x - 1, y] <;>
    simp only [hA, hB, hC, hD, not_true, not_false_iff, iff_true, iff_false] <;> norm_num


end Lattice
end StatMech
