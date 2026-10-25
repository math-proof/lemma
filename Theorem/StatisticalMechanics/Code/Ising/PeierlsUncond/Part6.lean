/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsFull.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Def.StatisticalMechanics.Code.Ising.PeierlsUncond.Part6
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


@[simp] lemma flipInteriorOnEquiv_apply {n : ℕ} (K : Set (Site d))
    (τ : {x // x ∈ box d n} → Bool) : flipInteriorOnEquiv K τ = flipInteriorOn K τ := rfl


lemma glue_flipInteriorOn {n : ℕ} (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (τ : {x // x ∈ box d n} → Bool) :
    glue η (flipInteriorOn K τ) = flipOnSet K (glue η τ) := by
  funext x
  unfold flipOnSet flipInteriorOn
  by_cases hx : x ∈ box d n
  · rw [glue_mem _ _ hx]
    by_cases hK' : x ∈ K
    · rw [if_pos hK', glue_mem _ _ hx, if_pos hK']
    · rw [if_neg hK', glue_mem _ _ hx, if_neg hK']
  · rw [glue_not_mem _ _ hx]
    have hxK : x ∉ K := fun h => hx (hK h)
    rw [if_neg hxK, glue_not_mem _ _ hx]


lemma fvEnergy_flipInteriorOn (n : ℕ) (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d)))
    (τ : {x // x ∈ box d n} → Bool) :
    fvEnergy η n B 0 (flipInteriorOn K τ)
      = fvEnergy η n B 0 τ + 2 * ∑ e ∈ B, crossEdgeBond K (glue η τ) e := by
  unfold fvEnergy
  rw [glue_flipInteriorOn K hK η τ]
  have hbond : (∑ e ∈ B, bond (flipOnSet K (glue η τ)) e)
      = (∑ e ∈ B, bond (glue η τ) e) + (-2) * ∑ e ∈ B, crossEdgeBond K (glue η τ) e := by
    have := bondSum_flipOnSet_diff K (glue η τ) B
    linarith [this]
  rw [hbond]
  ring


lemma fvWeight_flipInteriorOn (n : ℕ) (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d))) (β : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    fvWeight η n B β 0 (flipInteriorOn K τ)
      = Real.exp (-β * (2 * ∑ e ∈ B, crossEdgeBond K (glue η τ) e))
          * fvWeight η n B β 0 τ := by
  unfold fvWeight
  rw [fvEnergy_flipInteriorOn n K hK η B τ, mul_add, Real.exp_add]
  ring


lemma fvWeight_flipInteriorOn_eq_of_event (n : ℕ) (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d))) (β : ℝ)
    (τ : {x // x ∈ box d n} → Bool) (hev : ContourEvent K B (glue η τ)) :
    fvWeight η n B β 0 τ
      = Real.exp (-(2 * β) * (contourLen K B : ℝ))
          * fvWeight η n B β 0 (flipInteriorOn K τ) := by
  rw [fvWeight_flipInteriorOn n K hK η B β τ, sum_crossEdgeBond_event K (glue η τ) B hev]
  rw [← mul_assoc, ← Real.exp_add]
  rw [show (-(2 * β) * (contourLen K B : ℝ)) + (-β * (2 * -(contourLen K B : ℝ))) = 0 by ring]
  rw [Real.exp_zero, one_mul]


end Ising
end StatMech
