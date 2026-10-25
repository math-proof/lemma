/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanWindingConstruct
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jwn_marked_iff (H : SimpleGraph (Site 2)) (f0 g0 a b : Site 2) :
    (wcl_cutFlip H f0 g0 a b ∨ wcl_cutFlip H f0 g0 b a) ↔ wcl_cutFlip H f0 g0 a b := by
  unfold wcl_cutFlip whc_isCross
  rw [Sym2.eq_swap]; tauto


theorem jwn_cutColoring_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (jwn_cutCount H f0 g0 w) ↔ (φ x ↔ φ y) := by
  classical
  unfold jwn_cutCount
  induction w with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [wcl_flipCount_cons]
    
    have hkey : wcl_cutFlip H f0 g0 a b ↔ (φ a ↔ ¬ φ b) := hcut a b hab
    have hmk : (wcl_cutFlip H f0 g0 a b ∨ wcl_cutFlip H f0 g0 b a) ↔
        wcl_cutFlip H f0 g0 a b := jwn_marked_iff H f0 g0 a b
    by_cases hm : (wcl_cutFlip H f0 g0 a b ∨ wcl_cutFlip H f0 g0 b a)
    · rw [if_pos hm, add_comm, Nat.even_add_one, ih]
      have := hkey.mp (hmk.mp hm)
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all
    · rw [if_neg hm, zero_add, ih]
      have hnm : ¬ wcl_cutFlip H f0 g0 a b := fun h => hm (Or.inl h)
      have := fun hh => hnm (hkey.mpr hh)
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all


theorem jwn_no_cutColoring_of_oddLoop (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) (hodd : ¬ Even (jwn_cutCount H f0 g0 w)) :
    ¬ ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ := by
  rintro ⟨φ, hcut⟩
  exact hodd ((jwn_cutColoring_closedEven H f0 g0 φ hcut w).mpr Iff.rfl)


end Lattice
end StatMech
