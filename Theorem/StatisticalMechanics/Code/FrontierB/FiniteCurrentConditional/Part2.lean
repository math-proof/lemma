/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParityLift.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem parityFiberMass_closed (beta : ℝ) (hbeta : 0 ≤ beta)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    parityFiberMass G beta H =
      Real.cosh beta ^ G.edgeFinset.card * Real.tanh beta ^ H.card := by
  have hopen := fixedParity_weight_tsum G beta hbeta H hH
  have hclosed := fixedParity_weight_tsum_closed G beta hbeta H hH
  rw [hopen] at hclosed
  unfold parityFiberMass
  change (∏ e ∈ (Finset.univ : Finset G.edgeFinset),
      if e.1 ∈ H then Real.sinh beta else Real.cosh beta) = _
  rw [show (Finset.univ : Finset G.edgeFinset) = G.edgeFinset.attach by
    ext e
    simp]
  exact (Finset.prod_attach G.edgeFinset
    (fun e => if e ∈ H then Real.sinh beta else Real.cosh beta)).trans hclosed

theorem weight_eq_parityFiberMass_mul_kernel
    (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset)
    (m : EdgeCurrent G) (hm : currentParitySupport G m = H) :
    weight G beta (fun _ => 1) (ofEdgeFun G m) =
      parityFiberMass G beta H * parityCurrentKernel G beta H m := by
  have hall := (currentParitySupport_eq_iff G H hH m).mp hm
  unfold parityFiberMass parityCurrentKernel
  symm
  calc
    (∏ e : G.edgeFinset,
        if e.1 ∈ H then Real.sinh beta else Real.cosh beta) *
          ∏ e : G.edgeFinset,
            parityEdgeKernel beta (e.1 ∈ H) (m e) =
        ∏ e : G.edgeFinset,
          (if e.1 ∈ H then Real.sinh beta else Real.cosh beta) *
            parityEdgeKernel beta (e.1 ∈ H) (m e) := by
      exact (Finset.prod_mul_distrib (s := Finset.univ)).symm
    _ = ∏ e : G.edgeFinset,
          (beta * (fun _ => (1 : ℝ)) e.1) ^ m e / (m e).factorial := by
      apply Fintype.prod_congr
      intro e
      by_cases heH : e.1 ∈ H
      · have ho : Odd (m e) := by simpa [heH] using hall e
        have hsinh : Real.sinh beta ≠ 0 :=
          ne_of_gt (Real.sinh_pos_iff.2 hbeta)
        simp [parityEdgeKernel, heH, ho, conditionalCurrentTerm]
        field_simp [hsinh]
      · have hev : Even (m e) := by simpa [heH] using hall e
        have hcosh : Real.cosh beta ≠ 0 := ne_of_gt (Real.cosh_pos beta)
        simp [parityEdgeKernel, heH, hev, conditionalCurrentTerm]
        field_simp [hcosh]
    _ = weight G beta (fun _ => 1) (ofEdgeFun G m) :=
      (weight_ofEdgeFun G beta (fun _ => 1) m).symm

end StatMech.FrontierB
