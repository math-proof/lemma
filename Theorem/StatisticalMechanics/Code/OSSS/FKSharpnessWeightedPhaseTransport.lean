/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedCoherentLimit
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport
open MeasureTheory
open Set


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPhaseTransport

open Lattice FK Percolation

open FKSharpnessWeightedPeriodic

open FKSharpnessWeightedInfiniteVolume

variable {d : Nat}


theorem HasFiniteEnergyMerge.hasBoxFiniteEnergy
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hfe : HasFiniteEnergyMerge mu) : HasBoxFiniteEnergy mu :=
  fun n => hfe (boxEdges d n)


theorem clusterInfiniteEvent_subset_forceOpen_preimage
    (F : Finset (Sym2 (Site d))) (x y : Site d)
    (hconn : forall omega, Connected d (forceOpenFinset F omega) x y) :
    clusterInfiniteEvent d x <=
      forceOpenFinset F ⁻¹' clusterInfiniteEvent d y := by
  intro omega hx
  change (cluster d (forceOpenFinset F omega) y).Infinite
  have hx' : (cluster d (forceOpenFinset F omega) x).Infinite :=
    hx.mono (cluster_mono (forceOpenFinset_le F omega) x)
  rwa [cluster_eq_of_connected (hconn omega)] at hx'


theorem clusterInfiniteEvent_measure_pos_of_connector
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (F : Finset (Sym2 (Site d))) (x y : Site d)
    (hfe : mu.map (forceOpenFinset F) ≪ mu)
    (hconn : forall omega, Connected d (forceOpenFinset F omega) x y)
    (hx : 0 < mu (clusterInfiniteEvent d x)) :
    0 < mu (clusterInfiniteEvent d y) := by
  by_contra hy
  have hy0 : mu (clusterInfiniteEvent d y) = 0 :=
    nonpos_iff_eq_zero.mp (not_lt.mp hy)
  have hmap0 :
      (mu.map (forceOpenFinset F)) (clusterInfiniteEvent d y) = 0 :=
    hfe hy0
  have hpre0 :
      mu (forceOpenFinset F ⁻¹' clusterInfiniteEvent d y) = 0 := by
    rw [← Measure.map_apply (measurable_forceOpenFinset F)
      (measurableSet_clusterInfiniteEvent y)]
    exact hmap0
  have hle : mu (clusterInfiniteEvent d x) <=
      mu (forceOpenFinset F ⁻¹' clusterInfiniteEvent d y) :=
    measure_mono
      (clusterInfiniteEvent_subset_forceOpen_preimage F x y hconn)
  rw [hpre0] at hle
  exact (not_lt_of_ge hle) hx


theorem clusterInfiniteEvent_measure_pos_iff
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hfe : HasBoxFiniteEnergy mu) (x y : Site d) :
    0 < mu (clusterInfiniteEvent d x) <->
      0 < mu (clusterInfiniteEvent d y) := by
  obtain ⟨n, hn⟩ := finite_subset_box ({x, y} : Set (Site d))
    ((Set.finite_singleton y).insert x)
  have hxbox : x ∈ box d n := hn (Set.mem_insert x {y})
  have hybox : y ∈ box d n := hn (Set.mem_insert_of_mem x (Set.mem_singleton y))
  have hxy : forall omega,
      Connected d (forceOpenFinset (boxEdges d n) omega) x y :=
    fun omega => box_allOpen_connected omega hxbox hybox
  constructor
  · exact clusterInfiniteEvent_measure_pos_of_connector mu
      (boxEdges d n) x y (hfe n) hxy
  · exact clusterInfiniteEvent_measure_pos_of_connector mu
      (boxEdges d n) y x (hfe n) (fun omega => (hxy omega).symm)


theorem clusterInfiniteEvent_real_pos_iff
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsFiniteMeasure mu]
    (hfe : HasBoxFiniteEnergy mu) (x y : Site d) :
    0 < mu.real (clusterInfiniteEvent d x) <->
      0 < mu.real (clusterInfiniteEvent d y) := by
  have hxtop : mu (clusterInfiniteEvent d x) ≠ ⊤ := measure_ne_top mu _
  have hytop : mu (clusterInfiniteEvent d y) ≠ ⊤ := measure_ne_top mu _
  constructor
  · intro hx
    have hx0 : mu (clusterInfiniteEvent d x) ≠ 0 := by
      intro hz
      rw [Measure.real, hz] at hx
      simp at hx
    have hy := (clusterInfiniteEvent_measure_pos_iff mu hfe x y).mp
      (bot_lt_iff_ne_bot.mpr hx0)
    exact ENNReal.toReal_pos hy.ne' hytop
  · intro hy
    have hy0 : mu (clusterInfiniteEvent d y) ≠ 0 := by
      intro hz
      rw [Measure.real, hz] at hy
      simp at hy
    have hx := (clusterInfiniteEvent_measure_pos_iff mu hfe x y).mpr
      (bot_lt_iff_ne_bot.mpr hy0)
    exact ENNReal.toReal_pos hx.ne' hxtop


theorem shift_mem_clusterInfiniteEvent_iff
    (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    ConfigSpace.shift g omega ∈ clusterInfiniteEvent d (g • x) <->
      omega ∈ clusterInfiniteEvent d x := by
  change (cluster d (ConfigSpace.shift g omega) (g • x)).Infinite <->
    (cluster d omega x).Infinite
  rw [cluster_shift]
  exact Set.infinite_image_iff
    (Set.injOn_of_injective (smul_injective g))


theorem shift_preimage_clusterInfiniteEvent
    (g : Multiplicative (Site d)) (x : Site d) :
    (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) ->
      ConfigSpace (Sym2 (Site d))) ⁻¹'
        clusterInfiniteEvent d (g • x) =
      clusterInfiniteEvent d x := by
  ext omega
  exact shift_mem_clusterInfiniteEvent_iff g omega x


end FKSharpnessWeightedPhaseTransport
end OSSS
end StatMech
