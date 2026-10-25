/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Def.StatisticalMechanics.Code.Lattice.WindingColoring.Part4
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem wcl_cutFlip_symm (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) :
    wcl_SymmFlip (wcl_cutFlip H f0 g0) := by
  intro a b _hab
  unfold wcl_cutFlip whc_isCross
  rw [Sym2.eq_swap]
  tauto


theorem wcl_cutColoring_iff_compat (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) :
    whc_CutColoring H f0 g0 φ ↔
      ∀ a b, (hypercubicLattice 2).Adj a b →
        (wcl_cutFlip H f0 g0 a b ↔ (φ a ↔ ¬ φ b)) := Iff.rfl


theorem wcl_windingColoring_isCutColoring (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) (o : Site 2) :
    whc_CutColoring H f0 g0 (wcl_windingColoring (wcl_cutFlip H f0 g0) o) := by
  rw [wcl_cutColoring_iff_compat]
  intro a b hab
  exact wcl_windingColoring_compat (wcl_cutFlip H f0 g0) (wcl_cutFlip_symm H f0 g0) hce o hab


theorem wcl_flipCount_parity_of_compat (flip : Site 2 → Site 2 → Prop) (φ : Site 2 → Prop)
    (hcompat : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ (φ a ↔ ¬ φ b)))
    {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    Even (wcl_flipCount flip w) ↔ (φ x ↔ φ y) := by
  classical
  induction w with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [wcl_flipCount_cons]
    by_cases hcr : (flip a b ∨ flip b a)
    · rw [if_pos hcr, add_comm, Nat.even_add_one, ih]
      have hab' := (hcompat a b hab)
      have hba' := (hcompat b a hab.symm)
      have hf : flip a b := by
        rcases hcr with h | h
        · exact h
        · exact hab'.mpr (by have := hba'.mp h; tauto)
      have := hab'.mp hf
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all
    · rw [if_neg hcr, zero_add, ih]
      have hnf : ¬ flip a b := fun h => hcr (Or.inl h)
      have := fun hh => hnf ((hcompat a b hab).mpr hh)
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all


theorem wcl_closedEven_of_compat (flip : Site 2 → Site 2 → Prop) (φ : Site 2 → Prop)
    (hcompat : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ (φ a ↔ ¬ φ b))) :
    wcl_ClosedEven flip := by
  intro x w
  rw [wcl_flipCount_parity_of_compat flip φ hcompat w]


theorem wcl_no_cutColoring_of_odd_loop (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) (hodd : ¬ Even (wcl_flipCount (wcl_cutFlip H f0 g0) w)) :
    ¬ ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ := by
  rintro ⟨φ, hcut⟩
  rw [wcl_cutColoring_iff_compat] at hcut
  exact hodd (wcl_closedEven_of_compat (wcl_cutFlip H f0 g0) φ hcut w)


theorem wcl_exists_cutColoring_iff_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) :
    (∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ) ↔
      wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
  constructor
  · rintro ⟨φ, hcut⟩
    rw [wcl_cutColoring_iff_compat] at hcut
    exact wcl_closedEven_of_compat (wcl_cutFlip H f0 g0) φ hcut
  · intro hce
    exact ⟨wcl_windingColoring (wcl_cutFlip H f0 g0) ![0, 0],
      wcl_windingColoring_isCutColoring H f0 g0 hce ![0, 0]⟩


end Lattice
end StatMech
