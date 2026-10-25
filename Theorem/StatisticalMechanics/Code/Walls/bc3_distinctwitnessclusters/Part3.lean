/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_threewitnesses
import Theorem.StatisticalMechanics.Code.Walls.bc2_cutunbounded
import Def.StatisticalMechanics.Code.Walls.bc3_distinctwitnessclusters.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc3_threeArms_cutInfinite_of_residue (ω : ConfigSpace (Sym2 (Site d)))
    (hres : bc3_OriginCutLeavesInfinite ω) {x₁ x₂ x₃ : Site d}
    (hi1 : (cluster d ω x₁).Infinite) (hi2 : (cluster d ω x₂).Infinite)
    (hi3 : (cluster d ω x₃).Infinite) :
    ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧
      x₃' ∈ cluster d ω x₃ ∧
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite := by
  obtain ⟨x₁', hx₁', hinf₁⟩ := bc3_arm_cutInfinite_of_residue ω hres x₁ hi1
  obtain ⟨x₂', hx₂', hinf₂⟩ := bc3_arm_cutInfinite_of_residue ω hres x₂ hi2
  obtain ⟨x₃', hx₃', hinf₃⟩ := bc3_arm_cutInfinite_of_residue ω hres x₃ hi3
  exact ⟨x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃⟩


theorem bc3_distinctWitnessClusters (n : ℕ)
    (hres : ∀ ω ∈ threeMeetBox d n, bc3_OriginCutLeavesInfinite ω) :
    bc3_DistinctWitnessClusters d n := by
  intro ω hω
  obtain ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23⟩ :=
    bc2_threeWitnesses n ω hω
  obtain ⟨x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃⟩ :=
    bc3_threeArms_cutInfinite_of_residue ω (hres ω hω) hi1 hi2 hi3
  exact ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23,
    x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃⟩


theorem bc3_distinctWitnessClusters_nonvacuous (ω : ConfigSpace (Sym2 (Site d)))
    {x₁ x₂ x₃ : Site d}
    (hi1 : (cluster d ω x₁).Infinite) (hi2 : (cluster d ω x₂).Infinite)
    (hi3 : (cluster d ω x₃).Infinite)
    (h01 : (0 : Site d) ∉ cluster d ω x₁) (h02 : (0 : Site d) ∉ cluster d ω x₂)
    (h03 : (0 : Site d) ∉ cluster d ω x₃) :
    (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧
      (cluster d (removeSite 0 ω) x₃).Infinite :=
  ⟨bc3_cutClusterInfinite_of_originNotMem ω x₁ hi1 h01,
    bc3_cutClusterInfinite_of_originNotMem ω x₂ hi2 h02,
    bc3_cutClusterInfinite_of_originNotMem ω x₃ hi3 h03⟩


theorem bc3_originCutLeavesInfinite_of_origin_isolated (ω : ConfigSpace (Sym2 (Site d)))
    (hnone : ∀ x, (cluster d ω x).Infinite → (0 : Site d) ∉ cluster d ω x) :
    bc3_OriginCutLeavesInfinite ω := by
  intro x hinf h0
  exact absurd h0 (hnone x hinf)


theorem bc3_distinctWitnessClusters_node (n : ℕ) :
    ((∀ ω ∈ threeMeetBox d n, bc3_OriginCutLeavesInfinite ω) →
        bc3_DistinctWitnessClusters d n) ∧
      (∀ (ω : ConfigSpace (Sym2 (Site d))) {x₁ x₂ x₃ : Site d},
        (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
        cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
        cluster d ω x₂ ≠ cluster d ω x₃ →
        ((cluster d (removeSite 0 ω) x₁).Infinite ∧
            (cluster d (removeSite 0 ω) x₂).Infinite) ∨
          ((cluster d (removeSite 0 ω) x₁).Infinite ∧
            (cluster d (removeSite 0 ω) x₃).Infinite) ∨
          ((cluster d (removeSite 0 ω) x₂).Infinite ∧
            (cluster d (removeSite 0 ω) x₃).Infinite)) :=
  ⟨fun hres => bc3_distinctWitnessClusters n hres,
    fun ω {_ _ _} hi1 hi2 hi3 hd12 hd13 hd23 =>
      bc3_twoArms_cutInfinite ω hi1 hi2 hi3 hd12 hd13 hd23⟩

end Walls
end StatMech
