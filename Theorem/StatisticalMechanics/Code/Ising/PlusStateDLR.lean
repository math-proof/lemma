/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Def.StatisticalMechanics.Code.Ising.PlusStateDLR
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem specApply_eq_sum (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (f : ConfigSpace (Site d) → ℝ) (ω : ConfigSpace (Site d)) :
    specApply n B β h f ω
      = ∑ τ : {x // x ∈ box d n} → Bool, fvProb ω n B β h τ * f (glue ω τ) := by
  unfold specApply fvMeasure
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (fvProb_nonneg ω n B β h τ)]
  · intro τ _
    exact (integrable_dirac (by simp [enorm_eq_nnnorm])).smul_measure (by simp)


theorem continuous_glue (n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    Continuous (fun ω : ConfigSpace (Site d) => glue ω τ) := by
  refine continuous_pi (fun x => ?_)
  by_cases hx : x ∈ box d n
  · simp only [glue, hx, dif_pos]; exact continuous_const
  · simp only [glue, hx, dif_neg, not_false_iff]; exact continuous_apply x

theorem continuous_spin_glue (n : ℕ) (τ : {x // x ∈ box d n} → Bool) (x : Site d) :
    Continuous (fun ω : ConfigSpace (Site d) => spin (glue ω τ) x) :=
  (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℝ) else -1)).comp
    ((continuous_apply x).comp (continuous_glue n τ))

theorem continuous_bond_glue (n : ℕ) (τ : {x // x ∈ box d n} → Bool) (e : Sym2 (Site d)) :
    Continuous (fun ω : ConfigSpace (Site d) => bond (glue ω τ) e) := by
  induction e using Sym2.inductionOn with
  | hf x y => simp only [bond_mk]; exact (continuous_spin_glue n τ x).mul (continuous_spin_glue n τ y)

theorem continuous_fvEnergy (n : ℕ) (B : Finset (Sym2 (Site d))) (h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    Continuous (fun ω : ConfigSpace (Site d) => fvEnergy ω n B h τ) := by
  unfold fvEnergy
  refine Continuous.sub (Continuous.neg (continuous_finsetSum _ ?_))
    (Continuous.const_mul (continuous_finsetSum _ ?_) h)
  · intro e _; exact continuous_bond_glue n τ e
  · intro x _; exact continuous_spin_glue n τ x

theorem continuous_fvWeight (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    Continuous (fun ω : ConfigSpace (Site d) => fvWeight ω n B β h τ) := by
  unfold fvWeight
  exact Real.continuous_exp.comp ((continuous_fvEnergy n B h τ).const_mul (-β))

theorem continuous_fvZ (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    Continuous (fun ω : ConfigSpace (Site d) => fvZ ω n B β h) := by
  unfold fvZ
  exact continuous_finsetSum _ (fun τ _ => continuous_fvWeight n B β h τ)

theorem continuous_fvProb (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    Continuous (fun ω : ConfigSpace (Site d) => fvProb ω n B β h τ) := by
  unfold fvProb
  exact (continuous_fvWeight n B β h τ).div (continuous_fvZ n B β h)
    (fun ω => fvZ_ne_zero ω n B β h)


theorem specApply_continuous (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    {f : ConfigSpace (Site d) → ℝ} (hf : Continuous f) :
    Continuous (specApply n B β h f) := by
  have heq : specApply n B β h f
      = fun ω => ∑ τ : {x // x ∈ box d n} → Bool, fvProb ω n B β h τ * f (glue ω τ) := by
    funext ω; exact specApply_eq_sum n B β h f ω
  rw [heq]
  exact continuous_finsetSum _
    (fun τ _ => (continuous_fvProb n B β h τ).mul (hf.comp (continuous_glue n τ)))


end Ising
end StatMech
