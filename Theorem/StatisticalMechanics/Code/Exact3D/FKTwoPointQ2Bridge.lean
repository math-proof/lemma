/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FreeWiredAgreeClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Def.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


theorem freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2
    (d N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N) :
    Tendsto (fun m =>
      (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y))
      atTop
      (nhds ((freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y))) := by
  simpa [boxConnEvent] using
    (fk_free_infinite_measure (d := d) N hp hp1
      (S := connEvent (boxGraph d N) x y)
      (connEvent_isIncreasing (boxGraph d N) x y))


theorem tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
    (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    Tendsto (fun N =>
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n)
      atTop
      (nhds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)) := by
  simpa [freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume,
    freeInfiniteVolumeXAxisConnectionOfBetaQ2, freeInfiniteVolumeXAxisConnectionQ2]
    using freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2
      3 n (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)


theorem freeFiniteMeasure_real_boxConnEvent_mono_outer_q2
    (d : ℕ) {n M₁ M₂ : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (hM₁ : n ≤ M₁) (hM : M₁ ≤ M₂)
    (x y : boxVerts d n) :
    ((freeFiniteMeasure d M₁ hp hp1 (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d n x y)
      ≤
    ((freeFiniteMeasure d M₂ hp hp1 (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d n x y) := by
  have hmono := fkFreeLimit_monotone (d := d) n hp hp1
    (S := connEvent (boxGraph d n) x y)
    (connEvent_isIncreasing (boxGraph d n) x y)
  have hle := hmono (Nat.sub_le_sub_right hM n)
  have hM₂n : n ≤ M₂ := hM₁.trans hM
  have hM₁' : n + (M₁ - n) = M₁ := Nat.add_sub_of_le hM₁
  have hM₂' : n + (M₂ - n) = M₂ := Nat.add_sub_of_le hM₂n
  simpa [boxConnEvent, hM₁', hM₂'] using hle


theorem boxConnEvent_subset_full_boxConnEvent_of_le
    (d : ℕ) {n N : ℕ} (h : n ≤ N) (x y : boxVerts d n) :
    boxConnEvent d n x y ⊆
      boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y) := by
  intro ω hω
  rw [boxConnEvent, Set.mem_preimage] at hω ⊢
  rw [← boxRestrictLE_boxRestrict d h ω] at hω
  exact hω.map
    { toFun := boxVertInclLE d h
      map_rel' := by
        intro a b hab
        rw [openSub_adj] at hab ⊢
        constructor
        · simpa [boxGraph, boxVertInclLE] using hab.1
        · simpa [boxRestrictLE, innerEdgeLE] using hab.2 }


end Exact3D
end StatMech
