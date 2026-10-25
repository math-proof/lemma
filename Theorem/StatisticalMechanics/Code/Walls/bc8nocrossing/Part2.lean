/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc7nocrossing
import Theorem.StatisticalMechanics.Code.Walls.bc8distinctcutclusters.Part2
import Def.StatisticalMechanics.Code.Walls.bc8nocrossing
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc8_noCrossing (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    bc8_NoCrossing ω x y :=
  ⟨bc8_cut_ne_iff_disconnected, bc8_cut_disjoint_iff_disconnected, bc8_cut_no_crossing⟩


theorem bc8_threeArms_pairwiseDisjoint (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁' x₂' x₃' : Site d,
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite ∧
      Disjoint (cluster d (removeSite 0 ω) x₁') (cluster d (removeSite 0 ω) x₂') ∧
      Disjoint (cluster d (removeSite 0 ω) x₁') (cluster d (removeSite 0 ω) x₃') ∧
      Disjoint (cluster d (removeSite 0 ω) x₂') (cluster d (removeSite 0 ω) x₃') ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁' →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₂' →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁' →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃' →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₂' →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃' →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) := by
  obtain ⟨x₁', x₂', x₃', hinf₁, hinf₂, hinf₃, hd12, hd13, hd23⟩ :=
    bc8_threeArmClusters_distinct n ω hω
  exact ⟨x₁', x₂', x₃', hinf₁, hinf₂, hinf₃,
    bc8_disjoint_of_cut_ne hd12, bc8_disjoint_of_cut_ne hd13, bc8_disjoint_of_cut_ne hd23,
    bc8_cut_no_crossing hd12, bc8_cut_no_crossing hd13, bc8_cut_no_crossing hd23⟩


theorem bc8_threeArms_noCrossing (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁' x₂' x₃' : Site d,
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite ∧
      bc8_NoCrossing ω x₁' x₂' ∧ bc8_NoCrossing ω x₁' x₃' ∧ bc8_NoCrossing ω x₂' x₃' := by
  obtain ⟨x₁', x₂', x₃', hinf₁, hinf₂, hinf₃, _hd12, _hd13, _hd23⟩ :=
    bc8_threeArmClusters_distinct n ω hω
  exact ⟨x₁', x₂', x₃', hinf₁, hinf₂, hinf₃,
    bc8_noCrossing ω x₁' x₂', bc8_noCrossing ω x₁' x₃', bc8_noCrossing ω x₂' x₃'⟩


end Walls
end StatMech
