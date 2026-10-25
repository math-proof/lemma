/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem npm_kingAdj_P00_P11 (f : Site 2) : KingAdj (npd_P00 f) (npd_P11 f) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    simp only [npd_P00, npd_P11, Matrix.cons_val_zero] at h0
    omega
  · intro i
    fin_cases i <;> simp [npd_P00, npd_P11]


theorem npm_kingAdj_P10_P01 (f : Site 2) : KingAdj (npd_P10 f) (npd_P01 f) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    simp only [npd_P10, npd_P01, Matrix.cons_val_zero] at h0
    omega
  · intro i
    fin_cases i <;> simp [npd_P10, npd_P01]


theorem npm_diagTouch_outCorners_kingAdj {K : Set (Site 2)} {f : Site 2}
    (h : npd_DiagTouch K f) :
    (KingAdj (npd_P10 f) (npd_P01 f) ∧ npd_P10 f ∈ Kᶜ ∧ npd_P01 f ∈ Kᶜ) ∨
    (KingAdj (npd_P00 f) (npd_P11 f) ∧ npd_P00 f ∈ Kᶜ ∧ npd_P11 f ∈ Kᶜ) := by
  rcases h with ⟨_, _, h10, h01⟩ | ⟨_, _, h00, h11⟩
  · exact Or.inl ⟨npm_kingAdj_P10_P01 f, h10, h01⟩
  · exact Or.inr ⟨npm_kingAdj_P00_P11 f, h00, h11⟩


end Lattice
end StatMech
