/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalReduction
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityVaryingTemperature.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingMinusTIFromPlacement
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part3
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Lattice StatMech.ConfigSpace StatMech.FK
  StatMech.Sharpness

noncomputable section

variable {d : Nat}


theorem mem_criticalCenteredSlab_iff
    {L H : Nat} {x : Site 3} :
    x ∈ criticalCenteredSlab L H ↔
      (x 0).natAbs ≤ L ∧ (x 1).natAbs ≤ L ∧
        (x 2).natAbs ≤ H := by
  rw [criticalCenteredSlab, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨mem_boxFinset.mpr (fun i => ?_), h⟩
    fin_cases i
    · exact h.1.trans (Nat.le_max_left _ _)
    · exact h.2.1.trans (Nat.le_max_left _ _)
    · exact h.2.2.trans (Nat.le_max_right _ _)


theorem translatedBox_subset_criticalCenteredSlab
    (L H r : Nat) (x : Site 3)
    (hx0 : (x 0).natAbs + r ≤ L)
    (hx1 : (x 1).natAbs + r ≤ L)
    (hx2 : (x 2).natAbs + r ≤ H) :
    (boxFinset 3 r).image (fun y => Multiplicative.ofAdd x • y) ⊆
      criticalCenteredSlab L H := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_criticalCenteredSlab_iff]
  have hz' := mem_boxFinset.mp hz
  have hcoord (i : Fin 3) :
      ((Multiplicative.ofAdd x • z) i).natAbs ≤
        (x i).natAbs + r := by
    change (x i + z i).natAbs ≤ (x i).natAbs + r
    exact (Int.natAbs_add_le _ _).trans
      (Nat.add_le_add_left (hz' i) _)
  exact ⟨(hcoord 0).trans hx0, (hcoord 1).trans hx1,
    (hcoord 2).trans hx2⟩


theorem criticalCenteredSlab_spinUp_sub_abs_le_centeredGap
    (L H r : Nat) (x : Site 3)
    (hx0 : (x 0).natAbs + r ≤ L)
    (hx1 : (x 1).natAbs + r ≤ L)
    (hx2 : (x 2).natAbs + r ≤ H)
    (eta zeta : ConfigSpace (Site 3)) :
    |(gvMeasure eta (criticalCenteredSlab L H) (Ising.betaC 3) 0).real
          {omega | omega x = true} -
        (gvMeasure zeta (criticalCenteredSlab L H) (Ising.betaC 3) 0).real
          {omega | omega x = true}| ≤
      (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} -
        (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} :=
  gvMeasure_spinUp_sub_abs_le_critical_centeredGap
    (criticalCenteredSlab L H) eta zeta x r
    (translatedBox_subset_criticalCenteredSlab L H r x hx0 hx1 hx2)


theorem isingCritical_centeredSlab_origin_boundaryInfluence_tendsto_zero
    (L H : Nat -> Nat) (eta zeta : Nat -> ConfigSpace (Site 3))
    (hsize : Tendsto (fun n => min (L n) (H n)) atTop atTop) :
    Tendsto (fun n =>
      |(gvMeasure (eta n) (criticalCenteredSlab (L n) (H n))
            (Ising.betaC 3) 0).real
            {omega | omega (origin 3) = true} -
        (gvMeasure (zeta n) (criticalCenteredSlab (L n) (H n))
            (Ising.betaC 3) 0).real
            {omega | omega (origin 3) = true}|) atTop (nhds 0) := by
  let gap : Nat -> Real := fun r =>
    (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
        {omega | omega (origin 3) = true} -
      (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
        {omega | omega (origin 3) = true}
  have hgap : Tendsto gap atTop (nhds 0) := by
    exact isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero
      (origin 3)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (Filter.Eventually.of_forall fun n => by
      apply criticalCenteredSlab_spinUp_sub_abs_le_centeredGap
        (L n) (H n) (min (L n) (H n)) (origin 3)
      · simp [origin]
      · simp [origin]
      · simp [origin])
  exact hgap.comp hsize

end
end StatMech.FrontierA
