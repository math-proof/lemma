/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxCurrentParity
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Def.StatisticalMechanics.Code.FrontierB.PairSourceCurrentLimit
open Filter MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


theorem pairSourceBoxSite_ne {d n : ℕ} {x y : Site d}
    (hx : x ∈ box d n) (hy : y ∈ box d n) (hxy : x ≠ y) :
    pairSourceBoxSite x hx ≠ pairSourceBoxSite y hy := by
  intro h
  exact hxy (congrArg Subtype.val h)


theorem boxSpinSupport_pair {d n : ℕ} {x y : Site d}
    (hx : x ∈ box d n) (hy : y ∈ box d n) :
    boxSpinSupport d n {x, y} =
      {pairSourceBoxSite x hx, pairSourceBoxSite y hy} := by
  ext z
  simp only [boxSpinSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    rcases hz with hz | hz
    · left
      exact Subtype.ext hz
    · right
      exact Subtype.ext hz
  · rintro (hz | hz)
    · exact Or.inl (congrArg Subtype.val hz)
    · exact Or.inr (congrArg Subtype.val hz)


end StatMech.FrontierB
