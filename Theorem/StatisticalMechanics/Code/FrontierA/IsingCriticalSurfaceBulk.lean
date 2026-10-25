/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

theorem translatedBox_subset_boxFinset_of_margin
    {d n r : Nat} (x : Site d)
    (hmargin : forall k, (x k).natAbs + r <= n) :
    (boxFinset d r).image (fun y => Multiplicative.ofAdd x • y) <=
      boxFinset d n := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_boxFinset]
  intro k
  have hz' := mem_boxFinset.mp hz k
  change (x k + z k).natAbs <= n
  exact (Int.natAbs_add_le _ _).trans
    ((Nat.add_le_add_left hz' _).trans (hmargin k))


theorem oddPrismLowerHalfSurfaceSite_translatedBox_subset
    (n r : Nat) (i j : Fin (2 * n + 1))
    (hiLower : r <= i.val) (hiUpper : i.val + r <= 2 * n)
    (hjLower : r <= j.val) (hjUpper : j.val + r <= 2 * n) :
    (boxFinset 3 r).image (fun y =>
        Multiplicative.ofAdd
          (rectangularPrismSiteEquivSctBoxDobrushin n
            (oddPrismLowerHalfSurfaceSite n i j).1).1 • y) <=
      boxFinset 3 n := by
  apply translatedBox_subset_boxFinset_of_margin
  intro k
  fin_cases k
  · change ((rectangularPrismSiteEquivSctBoxDobrushin n
      (oddPrismLowerHalfSurfaceSite n i j).1).1 0).natAbs + r <= n
    rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_zero]
    dsimp [oddPrismLowerHalfSurfaceSite]
    omega
  · change ((rectangularPrismSiteEquivSctBoxDobrushin n
      (oddPrismLowerHalfSurfaceSite n i j).1).1 1).natAbs + r <= n
    rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_one]
    dsimp [oddPrismLowerHalfSurfaceSite]
    omega
  · change ((rectangularPrismSiteEquivSctBoxDobrushin n
      (oddPrismLowerHalfSurfaceSite n i j).1).1 2).natAbs + r <= n
    rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_two]
    dsimp [oddPrismLowerHalfSurfaceSite]
    omega


theorem oddPrismPlusSpinMean_nonneg
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    0 <= oddPrismPlusSpinMean beta n v := by
  unfold oddPrismPlusSpinMean
  rw [<- spinProd_singleton]
  apply ghsvp_expJ_nonneg
  · exact fun _ _ => hbeta
  · intro u
    exact mul_nonneg hbeta (Nat.cast_nonneg _)


theorem oddPrismPlusSpinMean_le_one
    (beta : Real) (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    oddPrismPlusSpinMean beta n v <= 1 := by
  unfold oddPrismPlusSpinMean expJ
  apply (div_le_one (ZJ_pos _ _ _)).2
  unfold ZJ
  apply Finset.sum_le_sum
  intro sigma _
  have hw : 0 <= wJ (oddPrismInternalEdges n) (fun _ => beta)
      (fun x => beta * oddPrismPlusField n x) sigma :=
    wJ_nonneg _ _ _ _
  have hs : spin sigma v <= 1 :=
    (le_abs_self _).trans (abs_spin_le_one sigma v)
  simpa [mul_comm] using mul_le_of_le_one_right hw hs


theorem isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap
    (n r : Nat) (i j : Fin (2 * n + 1))
    (hiLower : r <= i.val) (hiUpper : i.val + r <= 2 * n)
    (hjLower : r <= j.val) (hjUpper : j.val + r <= 2 * n) :
    oddPrismPlusSpinMean (Ising.betaC 3) n
        (oddPrismLowerHalfSurfaceSite n i j).1 <=
      (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} -
        (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} := by
  apply isingCritical_oddPrismPlusSpinMean_le_centeredGap
  exact oddPrismLowerHalfSurfaceSite_translatedBox_subset n r i j
    hiLower hiUpper hjLower hjUpper


theorem isingCritical_oddPrismPlusSurfaceSpinMean_tendsto_zero_of_margin
    (r : Nat -> Nat)
    (i j : (n : Nat) -> Fin (2 * n + 1))
    (hr : Tendsto r atTop atTop)
    (hiLower : forall n, r n <= (i n).val)
    (hiUpper : forall n, (i n).val + r n <= 2 * n)
    (hjLower : forall n, r n <= (j n).val)
    (hjUpper : forall n, (j n).val + r n <= 2 * n) :
    Tendsto (fun n =>
      oddPrismPlusSpinMean (Ising.betaC 3) n
        (oddPrismLowerHalfSurfaceSite n (i n) (j n)).1)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      oddPrismPlusSpinMean_nonneg (Ising.betaC 3)
        isingBetaC_three_pos.le n _
  · exact Filter.Eventually.of_forall fun n =>
      isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap
        n (r n) (i n) (j n)
          (hiLower n) (hiUpper n) (hjLower n) (hjUpper n)
  · exact (isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero
      (origin 3)).comp hr


end
end StatMech.FrontierA
