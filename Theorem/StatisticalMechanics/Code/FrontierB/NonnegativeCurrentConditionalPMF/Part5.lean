/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
import Def.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part5
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising


section Graph

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sourcelessNonnegativeParityPMF_apply
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (H : Finset (Sym2 V)) :
    sourcelessNonnegativeParityPMF G beta J hbeta.le hJ H =
      if _hH : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
        ENNReal.ofReal
            (inhomogeneousParityFiberMass G (fun e => beta * J e) H) *
          (ENNReal.ofReal (currentSum G beta J ∅))⁻¹
      else 0 := by
  classical
  rw [sourcelessNonnegativeParityPMF, PMF.map_apply]
  by_cases hvalid : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H
  · rw [dif_pos hvalid]
    have hsources (m : EdgeCurrent G)
        (hm : currentParitySupport G m = H) :
        sources G (ofEdgeFun G m) = ∅ := by
      apply (sources_empty_iff_currentParitySupport_even G m).2
      simpa [hm] using hvalid.2
    let f : EdgeCurrent G → ℝ := fun m =>
      if H = currentParitySupport G m then
        weight G beta J (ofEdgeFun G m) else 0
    have hfnonneg : ∀ m, 0 ≤ f m := by
      intro m
      unfold f
      split
      · unfold weight
        exact Finset.prod_nonneg fun e _ =>
          div_nonneg (pow_nonneg (mul_nonneg hbeta.le (hJ e)) _)
            (Nat.cast_nonneg _)
      · exact le_rfl
    have hfsummable : Summable f := by
      simpa only [f, eq_comm] using
        summable_fixedParity_weight_nonnegative G beta hbeta J
          (fun e => hJ e.1) H hvalid.1
    have hftsum : ∑' m, f m =
        inhomogeneousParityFiberMass G (fun e => beta * J e) H := by
      simpa only [f, eq_comm] using
        fixedParity_weight_tsum_nonnegative G beta hbeta J
          (fun e => hJ e.1) H hvalid.1
    calc
      _ = ∑' m : EdgeCurrent G,
            ENNReal.ofReal (f m) *
              (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ := by
        apply tsum_congr
        intro m
        by_cases hm : H = currentParitySupport G m
        · simp [f, hm, sourcelessCurrentPMF, currentPMF_apply,
            currentRawMass, hsources m hm.symm]
        · simp [f, hm]
      _ = (∑' m : EdgeCurrent G, ENNReal.ofReal (f m)) *
            (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ := by
        rw [ENNReal.tsum_mul_right]
      _ = ENNReal.ofReal (∑' m : EdgeCurrent G, f m) *
            (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ := by
        rw [ENNReal.ofReal_tsum_of_nonneg hfnonneg hfsummable]
      _ = _ := by rw [hftsum]
  · rw [dif_neg hvalid]
    rw [ENNReal.tsum_eq_zero]
    intro m
    by_cases hm : currentParitySupport G m = H
    · have hsub := currentParitySupport_subset G m
      have hnotEven : ¬ IsEvenSubgraph H := by
        intro heven
        exact hvalid ⟨hm ▸ hsub, heven⟩
      have hsrc : sources G (ofEdgeFun G m) ≠ ∅ := by
        intro hs
        apply hnotEven
        rw [← hm]
        exact (sources_empty_iff_currentParitySupport_even G m).1 hs
      simp [hm, sourcelessCurrentPMF, currentPMF_apply,
        currentRawMass, hsrc]
    · simp [Ne.symm hm]


theorem sourcelessCurrentPMF_apply_eq_nonnegativeParity_factor
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (m : EdgeCurrent G) :
    sourcelessCurrentPMF G beta J hbeta.le hJ m =
      sourcelessNonnegativeParityPMF G beta J hbeta.le hJ
          (currentParitySupport G m) *
        nonnegativeFiniteParityPMF G.edgeFinset (fun e => beta * J e)
          (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1))
          (fun e : G.edgeFinset => e.1 ∈ currentParitySupport G m) m := by
  let H := currentParitySupport G m
  have hH : H ⊆ G.edgeFinset := currentParitySupport_subset G m
  rw [sourcelessNonnegativeParityPMF_apply G beta hbeta J hJ H,
    nonnegativeFiniteParityPMF_apply]
  rw [sourcelessCurrentPMF, currentPMF_apply]
  by_cases hsrc : sources G (ofEdgeFun G m) = ∅
  · have heven : IsEvenSubgraph H :=
      (sources_empty_iff_currentParitySupport_even G m).1 hsrc
    rw [dif_pos ⟨hH, heven⟩]
    have hfactor := weight_eq_nonnegativeParityFiberMass_mul_kernel
      G beta hbeta J (fun e => hJ e.1) H hH m rfl
    have hfiber := inhomogeneousParityFiberMass_nonneg G
      (fun e => beta * J e) (fun e => mul_nonneg hbeta.le (hJ e.1)) H
    have hkernel : nonnegativeParityCurrentKernel G
          (fun e => beta * J e) H m =
        nonnegativeFiniteParityKernel G.edgeFinset (fun e => beta * J e)
          (fun e : G.edgeFinset => e.1 ∈ currentParitySupport G m) m := by
      simp only [nonnegativeParityCurrentKernel,
        nonnegativeFiniteParityKernel, H]
    rw [currentRawMass, if_pos hsrc, hfactor,
      ENNReal.ofReal_mul hfiber]
    change ENNReal.ofReal
          (inhomogeneousParityFiberMass G (fun e => beta * J e) H) *
        ENNReal.ofReal (nonnegativeParityCurrentKernel G
          (fun e => beta * J e) H m) *
          (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ = _
    rw [hkernel]
    ac_rfl
  · have hneven : ¬ IsEvenSubgraph H := by
      intro heven
      exact hsrc ((sources_empty_iff_currentParitySupport_even G m).2 heven)
    rw [dif_neg (fun h => hneven h.2)]
    simp [currentRawMass, hsrc]


theorem sourcelessCurrentPMF_eq_nonnegativeParity_bind
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) :
    sourcelessCurrentPMF G beta J hbeta.le hJ =
      (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).bind
        (fun H => nonnegativeFiniteParityPMF G.edgeFinset
          (fun e => beta * J e)
          (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1))
          (fun e : G.edgeFinset => e.1 ∈ H)) := by
  apply PMF.ext
  intro m
  rw [PMF.bind_apply,
    sourcelessCurrentPMF_apply_eq_nonnegativeParity_factor
      G beta hbeta J hJ m]
  symm
  rw [tsum_eq_single (currentParitySupport G m)]
  intro H hne
  by_cases hH : H ⊆ G.edgeFinset
  · have hk : nonnegativeParityCurrentKernel G
        (fun e => beta * J e) H m = 0 :=
      nonnegativeParityCurrentKernel_eq_zero_of_support_ne
        G (fun e => beta * J e) H hH m (Ne.symm hne)
    have hk' : nonnegativeFiniteParityKernel G.edgeFinset
        (fun e => beta * J e) (fun e : G.edgeFinset => e.1 ∈ H) m = 0 := by
      simpa only [nonnegativeFiniteParityKernel,
        nonnegativeParityCurrentKernel] using hk
    rw [nonnegativeFiniteParityPMF_apply]
    rw [hk']
    simp
  · rw [sourcelessNonnegativeParityPMF_apply G beta hbeta J hJ H]
    simp [hH]


theorem sourcelessCurrentPMF_map_eq_nonnegativeParity_bind
    {A : Type*} (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (f : EdgeCurrent G → A) :
    PMF.map f (sourcelessCurrentPMF G beta J hbeta.le hJ) =
      (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).bind
        (fun H => PMF.map f (nonnegativeFiniteParityPMF G.edgeFinset
          (fun e => beta * J e)
          (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1))
          (fun e : G.edgeFinset => e.1 ∈ H))) := by
  rw [sourcelessCurrentPMF_eq_nonnegativeParity_bind G beta hbeta J hJ,
    PMF.map_bind]

end Graph
end StatMech.FrontierB
