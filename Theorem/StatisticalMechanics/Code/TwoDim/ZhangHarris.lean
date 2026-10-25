/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part12
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Def.StatisticalMechanics.Code.TwoDim.ZhangHarris
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

theorem zih_clusterApprox_dependsOn (x : Site 2) (m : ℕ) :
    StatMech.DependsOn (zih_clusterApprox x m) (zih_clusterSupport x m) := by
  rw [zih_clusterApprox, crossingEvent_eq_boxCrossingEvent (m + 1) (by omega)]
  have hbase : StatMech.DependsOn (Percolation.boxCrossingEvent 2 (m + 1))
      (boxEdgeFinset 2 (m + 1) : Set (Sym2 (Site 2))) :=
    ih_event_dependsOn_of_indicator
      (Percolation.boxCrossingEvent_dependsOn (d := 2) (m + 1))
  intro omega omega' hagree
  apply hbase
  intro e he
  simp only [ConfigSpace.shift_apply]
  apply hagree
  rw [Finset.mem_coe, zih_clusterSupport, Finset.mem_image]
  exact ⟨e, by simpa using he, rfl⟩

theorem zih_clusterApprox_isIncreasing (x : Site 2) (m : ℕ) :
    IsIncreasing (zih_clusterApprox x m) := by
  rw [zih_clusterApprox, crossingEvent_eq_boxCrossingEvent (m + 1) (by omega)]
  intro omega omega' hle hmem
  exact Percolation.boxCrossingEvent_isIncreasing (m + 1) (fun e => hle _) hmem

theorem zih_clusterApprox_measurableSet (x : Site 2) (m : ℕ) :
    MeasurableSet (zih_clusterApprox x m) := by
  unfold zih_clusterApprox
  exact (measurableSet_crossingEvent (d := 2) (m + 1)).preimage
    (ConfigSpace.measurable_shift (zih_centerShift x))

theorem zih_clusterApprox_antitone (x : Site 2) : Antitone (zih_clusterApprox x) := by
  intro m n hmn omega hmem
  exact crossingEvent_antitone (m + 1) (n + 1) (by omega) hmem

theorem zih_cluster_shift_infinite_iff (omega : ConfigSpace (Sym2 (Site 2)))
    (x : Site 2) :
    (cluster 2 (ConfigSpace.shift (zih_centerShift x) omega) (origin 2)).Infinite ↔
      (cluster 2 omega x).Infinite := by
  have hg : zih_centerShift x • x = origin 2 := by
    funext i
    simp [zih_centerShift, smul_site_apply, origin]
  rw [← hg, cluster_shift]
  exact Set.infinite_image_iff
    ((MulAction.injective (zih_centerShift x) : Function.Injective
      (fun y : Site 2 => zih_centerShift x • y)).injOn)

theorem zih_clusterInfinite_eq_iInter (x : Site 2) :
    {omega : ConfigSpace (Sym2 (Site 2)) | (cluster 2 omega x).Infinite} =
      ⋂ m : ℕ, zih_clusterApprox x m := by
  ext omega
  rw [Set.mem_setOf_eq, ← zih_cluster_shift_infinite_iff omega x,
    ← Percolation.mem_percolationEvent, Percolation.percolationEvent_eq_iInter]
  simp only [zih_clusterApprox, Set.mem_iInter, Set.mem_preimage]

end StatMech.TwoDim
