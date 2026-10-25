/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Def.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part4
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem whc_correctWhitney_of_residue (hres : whc_WhitneyColoringResidue) :
    whb_CorrectWhitney := by
  intro H p q f0 g0 hpq hnpq hfg hshared
  obtain ⟨φ, hcut, htrack, hback⟩ := hres H p q f0 g0 hpq hnpq hfg hshared
  constructor
  · intro hreach
    exact whc_deleted_separated H f0 g0 φ hcut (htrack.mp hreach)
  · intro hsep
    by_contra hnr
    have hsame : (φ f0 ↔ φ g0) := by
      by_contra hdiff
      exact hnr (htrack.mpr hdiff)
    exact hsep (hback hsame)


theorem whc_shared_hstep (a0 a1 b1 : ℤ) :
    sharedPrimalEdge ![a0, a1] ![a0, b1] = s(![a0, max a1 b1], ![a0 + 1, max a1 b1]) := by
  unfold sharedPrimalEdge; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, if_true]


theorem whc_shared_vstep (a0 b0 a1 : ℤ) (h : a0 ≠ b0) :
    sharedPrimalEdge ![a0, a1] ![b0, a1] = s(![max a0 b0, a1], ![max a0 b0, a1 + 1]) := by
  unfold sharedPrimalEdge
  rw [if_neg (by simp only [Matrix.cons_val_zero]; exact h)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]


theorem whc_site_eq_iff (x : Site 2) (c d : ℤ) : x = ![c, d] ↔ x 0 = c ∧ x 1 = d := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> simp_all


end Lattice
end StatMech
