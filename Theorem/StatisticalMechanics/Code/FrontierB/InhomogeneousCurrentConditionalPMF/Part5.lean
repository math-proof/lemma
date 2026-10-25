/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Def.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness


section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem weight_eq_inhomogeneousParityFiberMass_mul_kernel
    (beta : Real) (hbeta : 0 < beta) (J : Sym2 V -> Real)
    (hJ : forall e : G.edgeFinset, 0 < J e.1)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset)
    (m : EdgeCurrent G) (hm : currentParitySupport G m = H) :
    weight G beta J (ofEdgeFun G m) =
      inhomogeneousParityFiberMass G (fun e => beta * J e) H *
        inhomogeneousParityCurrentKernel G (fun e => beta * J e) H m := by
  have hall := (currentParitySupport_eq_iff G H hH m).mp hm
  unfold inhomogeneousParityFiberMass inhomogeneousParityCurrentKernel
  symm
  calc
    (∏ e : G.edgeFinset,
        if e.1 ∈ H then Real.sinh (beta * J e.1)
        else Real.cosh (beta * J e.1)) *
          ∏ e : G.edgeFinset,
            parityEdgeKernel (beta * J e.1) (e.1 ∈ H) (m e) =
        ∏ e : G.edgeFinset,
          (if e.1 ∈ H then Real.sinh (beta * J e.1)
            else Real.cosh (beta * J e.1)) *
              parityEdgeKernel (beta * J e.1) (e.1 ∈ H) (m e) := by
      exact (Finset.prod_mul_distrib (s := Finset.univ)).symm
    _ = ∏ e : G.edgeFinset, (beta * J e.1) ^ m e / (m e).factorial := by
      apply Fintype.prod_congr
      intro e
      have hlambda : 0 < beta * J e.1 := mul_pos hbeta (hJ e)
      by_cases heH : e.1 ∈ H
      · have ho : Odd (m e) := by simpa [heH] using hall e
        have hsinh : Real.sinh (beta * J e.1) ≠ 0 :=
          ne_of_gt (Real.sinh_pos_iff.2 hlambda)
        simp [parityEdgeKernel, heH, ho, conditionalCurrentTerm]
        field_simp [hsinh]
      · have hev : Even (m e) := by simpa [heH] using hall e
        have hcosh : Real.cosh (beta * J e.1) ≠ 0 :=
          ne_of_gt (Real.cosh_pos (beta * J e.1))
        simp [parityEdgeKernel, heH, hev, conditionalCurrentTerm]
        field_simp [hcosh]
    _ = weight G beta J (ofEdgeFun G m) :=
      (weight_ofEdgeFun G beta J m).symm


theorem fixedParity_weight_tsum_inhomogeneous
    (beta : Real) (hbeta : 0 < beta) (J : Sym2 V -> Real)
    (hJ : forall e : G.edgeFinset, 0 < J e.1)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        weight G beta J (ofEdgeFun G m) else 0) =
      inhomogeneousParityFiberMass G (fun e => beta * J e) H := by
  let lambda : Sym2 V -> Real := fun e => beta * J e
  have hlambda : forall e : G.edgeFinset, 0 < lambda e.1 := fun e =>
    mul_pos hbeta (hJ e)
  let c := inhomogeneousParityFiberMass G lambda H
  let kernel := inhomogeneousParityCurrentKernel G lambda H
  have hpoint (m : EdgeCurrent G) :
      (if currentParitySupport G m = H then
          weight G beta J (ofEdgeFun G m) else 0) = c * kernel m := by
    by_cases hm : currentParitySupport G m = H
    · rw [if_pos hm]
      exact weight_eq_inhomogeneousParityFiberMass_mul_kernel
        G beta hbeta J hJ H hH m hm
    · rw [if_neg hm]
      have hk : kernel m = 0 := by
        exact inhomogeneousParityCurrentKernel_eq_zero_of_support_ne
          G lambda H hH m hm
      rw [hk, mul_zero]
  rw [tsum_congr hpoint, tsum_mul_left,
    tsum_inhomogeneousParityCurrentKernel G lambda hlambda H, mul_one]

end Graph
end StatMech.FrontierB
