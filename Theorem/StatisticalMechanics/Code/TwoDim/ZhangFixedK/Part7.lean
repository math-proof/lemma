/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part7
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_pairError_measurableSet (x y : Site 2) (N : ℕ) :
    MeasurableSet (zfk_pairError x y N) :=
  ((measurableSet_clusterInfinite x).inter
    (measurableSet_clusterInfinite y)).diff
      (zbd_connectedWithinBox_measurableSet x y N)

theorem zfk_pairError_antitone (x y : Site 2) :
    Antitone (zfk_pairError x y) := by
  intro n m hnm omega herror
  exact ⟨herror.1, fun hm => herror.2 (zbd_connectedWithinBox_mono x y hnm hm)⟩

theorem zfk_iInter_pairError_subset_atLeastTwo (x y : Site 2) :
    (⋂ N, zfk_pairError x y N) ⊆ atLeastTwoInfinite 2 := by
  intro omega herror
  have hzero := Set.mem_iInter.mp herror 0
  have hxinf := hzero.1.1
  have hyinf := hzero.1.2
  have hnconn : ¬ Connected 2 omega x y := by
    intro hxy
    obtain ⟨N, hxN, hyN, hwithin⟩ :=
      zbd_connectedWithin_box_of_connected omega hxy
    exact (Set.mem_iInter.mp herror N).2 ⟨hxN, hyN, hwithin⟩
  have hcx : cluster 2 omega x ∈ infiniteClusters 2 omega := ⟨hxinf, x, rfl⟩
  have hcy : cluster 2 omega y ∈ infiniteClusters 2 omega := ⟨hyinf, y, rfl⟩
  have hcne : cluster 2 omega x ≠ cluster 2 omega y := by
    intro heq
    have : y ∈ cluster 2 omega x := heq ▸ self_mem_cluster omega y
    exact hnconn this
  have hnt : (infiniteClusters 2 omega).Nontrivial :=
    ⟨_, hcx, _, hcy, hcne⟩
  have hone : (1 : ℕ∞) < (infiniteClusters 2 omega).encard :=
    Set.one_lt_encard_iff_nontrivial.mpr hnt
  show 2 ≤ numInfiniteClusters 2 omega
  rw [numInfiniteClusters, ← one_add_one_eq_two,
    ENat.add_one_le_iff ENat.one_ne_top]
  exact hone


theorem zfk_pairError_tendsto_zero (x y : Site 2) :
    Tendsto (fun N => halfMeasure.real (zfk_pairError x y N)) atTop (nhds 0) := by
  have hlim : Tendsto (fun N : ℕ => halfMeasure (zfk_pairError x y N)) atTop
      (nhds (halfMeasure (⋂ N, zfk_pairError x y N))) :=
    tendsto_measure_iInter_atTop
      (μ := halfMeasure)
      (fun N => (zfk_pairError_measurableSet x y N).nullMeasurableSet)
      (zfk_pairError_antitone x y)
      ⟨0, measure_ne_top halfMeasure _⟩
  have hinter : halfMeasure (⋂ N, zfk_pairError x y N) = 0 :=
    measure_mono_null (zfk_iInter_pairError_subset_atLeastTwo x y)
      zbd_atLeastTwo_halfMeasure_zero
  rw [hinter] at hlim
  exact (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ∞)).comp hlim


theorem zfk_rightCentralBox_finite (k : ℕ) :
    (zfk_rightCentralBox k).Finite := by
  have hinj : Function.Injective (fun x : Site 2 => x - ![1, 0]) := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    simp only [Pi.sub_apply] at hi
    omega
  exact Set.Finite.preimage hinj.injOn (box_finite 2 k)

end StatMech.TwoDim
