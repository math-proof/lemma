/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsUncond.Part11
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


lemma pcc_contourLen_empty (B : Finset (Sym2 (Site d))) :
    contourLen (∅ : Set (Site d)) B = 0 := by
  unfold contourLen crossEdges
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e _
  induction e with
  | h x y => rw [crosses_mk]; simp


lemma pcc_empty_mem_clusterFamily (n : ℕ) :
    (∅ : Finset (Site d)) ∈ clusterFamily (d := d) n :=
  Finset.empty_mem_powerset _


lemma pcc_one_le_sum (n : ℕ) (β : ℝ) :
    (1 : ℝ) ≤ ∑ K ∈ clusterFamily (d := d) n,
        Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
  have hemp : (∅ : Finset (Site d)) ∈ clusterFamily (d := d) n :=
    pcc_empty_mem_clusterFamily n
  have hcl0 : contourLen ((∅ : Finset (Site d)) : Set (Site d)) (bondFinsetTouch d n) = 0 := by
    have hco : ((∅ : Finset (Site d)) : Set (Site d)) = ∅ := by simp
    rw [hco]; exact pcc_contourLen_empty _
  have hle := Finset.single_le_sum
      (f := fun K : Finset (Site d) =>
        Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)))
      (s := clusterFamily (d := d) n)
      (fun K _ => by positivity) hemp
  simp only [hcl0, Nat.cast_zero, mul_zero, Real.exp_zero] at hle
  exact hle


theorem pcc_not_contourCountBound :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → ¬ ContourCountBound d n β := by
  obtain ⟨β₀, hβ₀⟩ := exists_beta_peierlsBound_lt_half d
  refine ⟨β₀, fun n β hβ hCount => ?_⟩
  have h1 : (1 : ℝ) ≤ ∑ K ∈ clusterFamily (d := d) n,
      Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := pcc_one_le_sum n β
  have h2 : peierlsBound d β < 1 / 2 := hβ₀ β hβ
  have hle : (1 : ℝ) ≤ peierlsBound d β := le_trans h1 hCount
  linarith


end Ising
end StatMech
