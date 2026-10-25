/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivativeLower
import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationFK
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part5
open scoped BigOperators
open Finset
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem oddPrismPlus_wJ_eq_fvWeight
    (beta : Real) (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    wJ (oddPrismInternalEdges n) (fun _ => beta)
        (fun x => beta * oddPrismPlusField n x) sigma =
      fvWeight (plusField 3) n (bondFinsetTouch 3 n) beta 0
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma) := by
  rw [show wJ (oddPrismInternalEdges n) (fun _ => beta)
      (fun x => beta * oddPrismPlusField n x) sigma =
      Real.exp (beta * inhomogeneousInteraction (oddPrismInternalEdges n)
        (fun _ => 1) (oddPrismPlusField n) sigma) by
        simpa using scaled_wJ_eq_exp_interaction
          (oddPrismInternalEdges n) (fun _ => 1)
          (oddPrismPlusField n) sigma beta]
  rw [oddPrism_plus_inhomogeneousInteraction,
    rectangularPrismPlusEnergy_eq_mul_fvEnergy]
  unfold fvWeight
  congr 1
  ring

theorem oddPrismPlus_ZJ_eq_fvZ (beta : Real) (n : Nat) :
    ZJ (oddPrismInternalEdges n) (fun _ => beta)
        (fun x => beta * oddPrismPlusField n x) =
      fvZ (plusField 3) n (bondFinsetTouch 3 n) beta 0 := by
  calc
    _ = scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1)
        (oddPrismPlusField n) beta := by
      unfold scaledInhomogeneousPartition
      congr 2 <;> funext x <;> ring
    _ = rectangularPrismPlusPartition 1 beta
        (2 * n + 1) (2 * n + 1) n :=
      scaledInhomogeneousPartition_oddPrismPlus beta n
    _ = _ := by
      simpa using rectangularPrismPlusPartition_eq_fvZ 1 beta n


theorem oddPrismPlusSpinMean_eq_plusMeasure_integral
    (beta : Real) (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    oddPrismPlusSpinMean beta n v =
      ∫ omega, spin omega
          (rectangularPrismSiteEquivSctBoxDobrushin n v).1
        ∂(plusMeasure 3 n beta 0 : Measure (ConfigSpace (Site 3))) := by
  rw [plusMeasure_coe, integral_fvMeasure_eq_sum]
  unfold oddPrismPlusSpinMean expJ fvProb
  rw [oddPrismPlus_ZJ_eq_fvZ]
  have hsum :
      (∑ tau : {x // x ∈ box 3 n} -> Bool,
        fvWeight (plusField 3) n (bondFinsetTouch 3 n) beta 0 tau /
            fvZ (plusField 3) n (bondFinsetTouch 3 n) beta 0 *
          spin (glue (plusField 3) tau)
            (rectangularPrismSiteEquivSctBoxDobrushin n v).1) =
        (∑ tau : {x // x ∈ box 3 n} -> Bool,
          fvWeight (plusField 3) n (bondFinsetTouch 3 n) beta 0 tau *
            spin (glue (plusField 3) tau)
              (rectangularPrismSiteEquivSctBoxDobrushin n v).1) /
          fvZ (plusField 3) n (bondFinsetTouch 3 n) beta 0 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro tau _
    ring
  rw [hsum]
  congr 1
  rw [← Equiv.sum_comp (rectangularPrismConfigEquivSctBoxDobrushin n)]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [oddPrismPlus_wJ_eq_fvWeight,
    spin_glue_rectangularPrismConfigEquiv]
  ring


end
end StatMech.FrontierA
