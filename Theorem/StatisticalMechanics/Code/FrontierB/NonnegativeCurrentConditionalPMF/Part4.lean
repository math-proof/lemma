/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
import Def.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part4
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising


section Graph

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem summable_nonnegativeParityCurrentKernel
    (lambda : Sym2 V → ℝ)
    (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1)
    (H : Finset (Sym2 V)) :
    Summable (nonnegativeParityCurrentKernel G lambda H) := by
  simpa only [nonnegativeParityCurrentKernel,
    nonnegativeFiniteParityKernel] using
      summable_nonnegativeFiniteParityKernel G.edgeFinset lambda hlambda
        (fun e : G.edgeFinset => e.1 ∈ H)

theorem tsum_nonnegativeParityCurrentKernel
    (lambda : Sym2 V → ℝ)
    (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1)
    (H : Finset (Sym2 V)) :
    ∑' m : EdgeCurrent G,
      nonnegativeParityCurrentKernel G lambda H m = 1 := by
  simpa only [nonnegativeParityCurrentKernel,
    nonnegativeFiniteParityKernel] using
      tsum_nonnegativeFiniteParityKernel G.edgeFinset lambda hlambda
        (fun e : G.edgeFinset => e.1 ∈ H)

theorem nonnegativeParityCurrentKernel_eq_zero_of_support_ne
    (lambda : Sym2 V → ℝ) (H : Finset (Sym2 V))
    (hH : H ⊆ G.edgeFinset) (m : EdgeCurrent G)
    (hm : currentParitySupport G m ≠ H) :
    nonnegativeParityCurrentKernel G lambda H m = 0 := by
  have hall : ¬(∀ e : G.edgeFinset,
      if e.1 ∈ H then Odd (m e) else Even (m e)) :=
    fun h => hm ((currentParitySupport_eq_iff G H hH m).mpr h)
  push Not at hall
  obtain ⟨e, he⟩ := hall
  unfold nonnegativeParityCurrentKernel
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  apply nonnegativeParityEdgeKernel_eq_zero_of_parity_ne
  by_cases heH : e.1 ∈ H <;> simpa [heH] using he


theorem weight_eq_nonnegativeParityFiberMass_mul_kernel
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e : G.edgeFinset, 0 ≤ J e.1)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset)
    (m : EdgeCurrent G) (hm : currentParitySupport G m = H) :
    weight G beta J (ofEdgeFun G m) =
      inhomogeneousParityFiberMass G (fun e => beta * J e) H *
        nonnegativeParityCurrentKernel G (fun e => beta * J e) H m := by
  have hall := (currentParitySupport_eq_iff G H hH m).mp hm
  unfold inhomogeneousParityFiberMass nonnegativeParityCurrentKernel
  symm
  calc
    (∏ e : G.edgeFinset,
        if e.1 ∈ H then Real.sinh (beta * J e.1)
        else Real.cosh (beta * J e.1)) *
          ∏ e : G.edgeFinset,
            nonnegativeParityEdgeKernel
              (beta * J e.1) (e.1 ∈ H) (m e) =
        ∏ e : G.edgeFinset,
          (if e.1 ∈ H then Real.sinh (beta * J e.1)
            else Real.cosh (beta * J e.1)) *
              nonnegativeParityEdgeKernel
                (beta * J e.1) (e.1 ∈ H) (m e) := by
      exact (Finset.prod_mul_distrib (s := Finset.univ)).symm
    _ = ∏ e : G.edgeFinset,
        (beta * J e.1) ^ m e / (m e).factorial := by
      apply Fintype.prod_congr
      intro e
      by_cases heH : e.1 ∈ H
      · simpa [heH] using
          parityFiberMass_mul_nonnegativeParityEdgeKernel
            (mul_nonneg hbeta.le (hJ e)) true (m e)
            (by simpa [heH] using hall e)
      · simpa [heH] using
          parityFiberMass_mul_nonnegativeParityEdgeKernel
            (mul_nonneg hbeta.le (hJ e)) false (m e)
            (by simpa [heH] using hall e)
    _ = weight G beta J (ofEdgeFun G m) :=
      (weight_ofEdgeFun G beta J m).symm

theorem summable_fixedParity_weight_nonnegative
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e : G.edgeFinset, 0 ≤ J e.1)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    Summable (fun m : EdgeCurrent G =>
      if currentParitySupport G m = H then
        weight G beta J (ofEdgeFun G m) else 0) := by
  let lambda : Sym2 V → ℝ := fun e => beta * J e
  let c := inhomogeneousParityFiberMass G lambda H
  let kernel := nonnegativeParityCurrentKernel G lambda H
  have hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1 := fun e =>
    mul_nonneg hbeta.le (hJ e)
  have hpoint (m : EdgeCurrent G) :
      (if currentParitySupport G m = H then
          weight G beta J (ofEdgeFun G m) else 0) = c * kernel m := by
    by_cases hm : currentParitySupport G m = H
    · rw [if_pos hm]
      exact weight_eq_nonnegativeParityFiberMass_mul_kernel
        G beta hbeta J hJ H hH m hm
    · rw [if_neg hm]
      have hk : kernel m = 0 :=
        nonnegativeParityCurrentKernel_eq_zero_of_support_ne
          G lambda H hH m hm
      rw [hk, mul_zero]
  exact ((summable_nonnegativeParityCurrentKernel G lambda hlambda H).mul_left c).congr
    (fun m => (hpoint m).symm)


theorem fixedParity_weight_tsum_nonnegative
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e : G.edgeFinset, 0 ≤ J e.1)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        weight G beta J (ofEdgeFun G m) else 0) =
      inhomogeneousParityFiberMass G (fun e => beta * J e) H := by
  let lambda : Sym2 V → ℝ := fun e => beta * J e
  have hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1 := fun e =>
    mul_nonneg hbeta.le (hJ e)
  let c := inhomogeneousParityFiberMass G lambda H
  let kernel := nonnegativeParityCurrentKernel G lambda H
  have hpoint (m : EdgeCurrent G) :
      (if currentParitySupport G m = H then
          weight G beta J (ofEdgeFun G m) else 0) = c * kernel m := by
    by_cases hm : currentParitySupport G m = H
    · rw [if_pos hm]
      exact weight_eq_nonnegativeParityFiberMass_mul_kernel
        G beta hbeta J hJ H hH m hm
    · rw [if_neg hm]
      have hk : kernel m = 0 :=
        nonnegativeParityCurrentKernel_eq_zero_of_support_ne
          G lambda H hH m hm
      rw [hk, mul_zero]
  rw [tsum_congr hpoint, tsum_mul_left,
    tsum_nonnegativeParityCurrentKernel G lambda hlambda H, mul_one]


end Graph
end StatMech.FrontierB
