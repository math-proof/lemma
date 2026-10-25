/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanCrossSource.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanHdom.Part2
import Notation.StatisticalMechanics.Code.Ising.AizenmanCrossSource
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness.RandomCurrent


local notation "srcK" => StatMech.Sharpness.RandomCurrent.sources

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem gha_crossSource_mass_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {x, y}) = aie_mass ends m φ A
      ∧ aie_mass ends m φ (A ∆ {o, y}) = aie_mass ends m φ A
      ∧ aie_mass ends m φ (A ∆ {o, x}) = aie_mass ends m φ A :=
  ⟨ahd_mass_reroute_xy_eq ends m hnd A hm hxy φ hφ hall,
   ahd_mass_reroute_oy_eq ends m hnd A hm hoy φ hφ hall,
   ahd_mass_reroute_ox_eq ends m hnd A hm hox φ hφ hall⟩


theorem gha_crossSource_total_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {x, y}) + aie_mass ends m φ (A ∆ {o, y})
        + aie_mass ends m φ (A ∆ {o, x})
      = 3 * aie_mass ends m φ A := by
  obtain ⟨h1, h2, h3⟩ := gha_crossSource_mass_eq ends m hnd A hm hox hoy hxy φ hφ hall
  rw [h1, h2, h3]; ring


theorem gha_allConn_gap_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A :=
  ahd_gap_eq_neg_two_mass ends m hnd A hm hox hoy hxy φ hφ hall


end Ising
end StatMech
