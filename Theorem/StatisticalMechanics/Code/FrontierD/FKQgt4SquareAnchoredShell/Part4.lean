/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareBoxClusterUnion
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4CriticalFreeShellSummability
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4WiredPhaseInput.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareAnchoredShell.Part4
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

open StatMech.Universality

noncomputable section

theorem measurableSet_inverseDualHasInfiniteClusterEvent :
    MeasurableSet inverseDualHasInfiniteClusterEvent := by
  exact (measurable_inverseFaceDualConfig
    (measurableSet_hasInfiniteClusterEvent 2))

theorem mem_limsup_atTop_of_forall_exists_ge
    {alpha : Type*} (A : Nat → Set alpha) (x : alpha)
    (h : ∀ n, ∃ j ≥ n, x ∈ A j) :
    x ∈ limsup A atTop := by
  rw [Filter.limsup_eq_iInf_iSup]
  change x ∈ ⋂ s ∈ atTop, ⋃ a ∈ s, A a
  simp only [Set.mem_iInter, Set.mem_iUnion]
  intro s hs
  rw [Filter.mem_atTop_sets] at hs
  obtain ⟨n, hn⟩ := hs
  obtain ⟨j, hj, hx⟩ := h n
  exact ⟨j, hn j hj, hx⟩


theorem inverseDualHasInfiniteClusterEvent_compl_subset_axis_limsup :
    inverseDualHasInfiniteClusterEventᶜ ⊆
      limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop := by
  intro omega hno
  have hfinite : ∀ x : Site 2,
      (cluster 2 (inverseFaceDualConfig omega) x).Finite := by
    intro x
    rw [← Set.not_infinite]
    intro hinf
    apply hno
    unfold inverseDualHasInfiniteClusterEvent hasInfiniteClusterEvent
    rw [Set.mem_preimage, Set.mem_iUnion]
    exact ⟨x, hinf⟩
  apply mem_limsup_atTop_of_forall_exists_ge
  intro n
  exact exists_axisAnchoredSphereConnection_of_inverseDual_clusters_finite
    omega n hfinite


theorem fkQgt4CriticalFreeAxisAnchoredSphereConnectionEvent_limsup_zero_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
        (limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop) = 0 := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) ≤ q := by linarith
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  have htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu := by
    simpa [mu, hp, hp1, hq0] using
      (FK.fkgqt_freeIV_isTranslationInvariant (d := 2) hp hp1 hq1)
  have hsum : (∑' j : Nat,
      mu (fkQgt4AxisAnchoredSphereConnectionEvent j)) ≠ ⊤ := by
    simp_rw [fkQgt4AxisAnchoredSphereConnectionEvent_measure_eq mu htrans]
    simpa [mu, hp, hp1, hq0] using
      fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_winding hq hwind
  change mu (limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop) = 0
  exact measure_limsup_atTop_eq_zero hsum


theorem fkQgt4CriticalFree_inverseDualHasInfiniteClusterEvent_eq_one_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
        inverseDualHasInfiniteClusterEvent = 1 := by
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q)
  have hzero : mu inverseDualHasInfiniteClusterEventᶜ = 0 := by
    apply le_antisymm
    · calc
        mu inverseDualHasInfiniteClusterEventᶜ ≤
            mu (limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop) :=
          measure_mono inverseDualHasInfiniteClusterEvent_compl_subset_axis_limsup
        _ = 0 := by
          simpa [mu] using
            fkQgt4CriticalFreeAxisAnchoredSphereConnectionEvent_limsup_zero_of_winding
              hq hwind
    · exact bot_le
  change mu inverseDualHasInfiniteClusterEvent = 1
  exact (prob_compl_eq_zero_iff
    measurableSet_inverseDualHasInfiniteClusterEvent).1 hzero

end
end StatMech.FrontierD
