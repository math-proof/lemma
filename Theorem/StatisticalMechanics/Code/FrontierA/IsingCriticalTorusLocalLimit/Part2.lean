/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryMonomialComparison.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityCriticalAxisClosure
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPhaseEndpoint
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalLimit.Part2
open Filter Finset MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

theorem mapped_boxSupport_eq_torusImage
    {d n : Nat} (A : Finset (Site d))
    (hA : (↑A : Set (Site d)) ⊆ box d n)
    (hinj : Set.InjOn (isingSiteToDyadicTorus n)
      (↑(boxFinset d n) : Set (Site d))) :
    (((boxFinsetSpinSupport d n A).map
        (isingTorusImageEquiv (boxFinset d n) hinj).toEmbedding).map
      (Function.Embedding.subtype fun z ↦
        z ∈ isingTorusImageFinset n (boxFinset d n))) =
      A.image (isingSiteToDyadicTorus n) := by
  ext z
  simp only [Finset.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x.1, by simpa [boxFinsetSpinSupport] using hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    let xBox : {x : Site d // x ∈ boxFinset d n} :=
      ⟨x, mem_boxFinset.mpr (hA hx)⟩
    let xT := isingTorusImageEquiv (boxFinset d n) hinj xBox
    refine ⟨xT, ?_, rfl⟩
    refine ⟨xBox, ?_, ?_⟩
    · simp [boxFinsetSpinSupport, xBox, hx]
    · apply Subtype.ext
      rfl

set_option maxHeartbeats 800000 in


theorem criticalTorusLocalSpinProd_tendsto
    {d : Nat} (hd : 2 < d) (A : Finset (Site d)) :
    Tendsto (criticalTorusLocalSpinProd d A) atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
          Measure (ConfigSpace (Site d))))) := by
  let betaC := IsingFK.betaC (magnetization d)
  have hbeta : 0 ≤ betaC := by
    dsimp [betaC]
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 ≤ d)]
    exact (tildeBetaCIsing_pos (by omega : 2 ≤ d)).le
  have hfree := integral_freeMeasure_spinProd_tendsto_freeState
    d betaC hbeta A
  have hplus := integral_plusMeasure_spinProd_full_tendsto
    d betaC hbeta A
  have hstates := criticalFreeState_eq_plusState hd
  have hplus' : Tendsto
      (fun n ↦ ∫ omega, spinProd A omega
        ∂(plusMeasure d n betaC 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d betaC 0 : Measure (ConfigSpace (Site d))))) := by
    rw [hstates]
    exact hplus
  obtain ⟨N, hAN⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  have hbounds : ∀ᶠ n in atTop,
      (∫ omega, spinProd A omega
          ∂(freeMeasure d n betaC 0 : Measure (ConfigSpace (Site d)))) ≤
        criticalTorusLocalSpinProd d A n ∧
      criticalTorusLocalSpinProd d A n ≤
        ∫ omega, spinProd A omega
          ∂(plusMeasure d n betaC 0 : Measure (ConfigSpace (Site d))) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hA : (↑A : Set (Site d)) ⊆ box d n :=
      hAN.trans (box_mono d hn)
    let S := boxFinset d n
    have hS : (↑S : Set (Site d)) ⊆ box d n := by
      intro x hx
      exact mem_boxFinset.mp hx
    let hinj : Set.InjOn (isingSiteToDyadicTorus n) (↑S : Set (Site d)) :=
      isingSiteToDyadicTorus_injectiveOn_finset S hS
        (by
          exact lt_of_lt_of_le (by omega : 2 * n < 2 * (n + 1))
            (two_mul_succ_lt_isingDyadicSide n).le)
    let B := boxFinsetSpinSupport d n A
    have hsandwich := freeSpinProd_le_isingTorusSpinProd_le_gvPlus
      S hS (two_mul_succ_lt_isingDyadicSide n) hinj betaC hbeta B
    have hfintype : (Finset.Subtype.fintype S) =
        (inferInstance : Fintype {x : Site d // x ∈ S}) :=
      Subsingleton.elim _ _
    rw [hfintype] at hsandwich
    have hmap := mapped_boxSupport_eq_torusImage A hA hinj
    have hBambient : B.map
        (Function.Embedding.subtype fun x ↦ x ∈ S) = A := by
      exact boxFinsetSpinSupport_map_subtype A hA
    constructor
    · rw [← isingExpectation_boxFinsetSpinSupport_eq_freeMeasure
        betaC A hA]
      change isingExpectation (graphS d S) betaC 0 (spinProd B) ≤ _
      rw [criticalTorusLocalSpinProd, ← hmap]
      exact hsandwich.1
    · rw [criticalTorusLocalSpinProd, ← hmap]
      calc
        _ ≤ ∫ omega, spinProd (B.map
              (Function.Embedding.subtype fun x ↦ x ∈ S)) omega
            ∂(gvPlusMeasure S betaC 0) := hsandwich.2
        _ = ∫ omega, spinProd A omega
            ∂(plusMeasure d n betaC 0 : Measure (ConfigSpace (Site d))) := by
          rw [hBambient, iptp_gvPlusMeasure_eq_plusMeasure]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hfree hplus' (hbounds.mono fun n hn ↦ hn.1)
      (hbounds.mono fun n hn ↦ hn.2)

end
end StatMech.FrontierA
