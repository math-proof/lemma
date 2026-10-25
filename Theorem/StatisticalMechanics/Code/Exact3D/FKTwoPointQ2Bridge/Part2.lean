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
import Def.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part2
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


theorem full_boxConnEvent_eq_inner_union_detour_of_le
    (d : ℕ) {n N : ℕ} (h : n ≤ N) (x y : boxVerts d n) :
    boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y) =
      boxConnEvent d n x y ∪ boxConnectionDetourEvent d h x y := by
  apply Set.Subset.antisymm
  · intro ω hω
    by_cases hinner : ω ∈ boxConnEvent d n x y
    · exact Or.inl hinner
    · exact Or.inr ⟨hω, hinner⟩
  · intro ω hω
    rcases hω with hinner | hdetour
    · exact boxConnEvent_subset_full_boxConnEvent_of_le d h x y hinner
    · exact hdetour.1


theorem measureReal_full_boxConnEvent_eq_inner_add_detour
    (d : ℕ) (μ : Measure (ConfigSpace (Sym2 (Lattice.Site d))))
    [IsFiniteMeasure μ]
    {n N : ℕ} (h : n ≤ N) (x y : boxVerts d n) :
    μ.real (boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y)) =
      μ.real (boxConnEvent d n x y) +
        μ.real (boxConnectionDetourEvent d h x y) := by
  have hdisj :
      Disjoint (boxConnEvent d n x y) (boxConnectionDetourEvent d h x y) := by
    exact Set.disjoint_left.mpr (by
      intro ω hinner hdetour
      exact hdetour.2 hinner)
  have hdetour_meas : MeasurableSet (boxConnectionDetourEvent d h x y) := by
    unfold boxConnectionDetourEvent
    exact (measurableSet_boxConnEvent d N
      (boxVertInclLE d h x) (boxVertInclLE d h y)).diff
        (measurableSet_boxConnEvent d n x y)
  calc
    μ.real (boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y))
        = μ.real (boxConnEvent d n x y ∪ boxConnectionDetourEvent d h x y) := by
          rw [full_boxConnEvent_eq_inner_union_detour_of_le]
    _ = μ.real (boxConnEvent d n x y) +
        μ.real (boxConnectionDetourEvent d h x y) :=
          measureReal_union hdisj hdetour_meas


theorem measureReal_full_boxConnEvent_le_inner_add_detour
    (d : ℕ) (μ : Measure (ConfigSpace (Sym2 (Lattice.Site d))))
    {n N : ℕ} (h : n ≤ N) (x y : boxVerts d n) :
    μ.real (boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y)) ≤
      μ.real (boxConnEvent d n x y) +
        μ.real (boxConnectionDetourEvent d h x y) := by
  calc
    μ.real (boxConnEvent d N (boxVertInclLE d h x) (boxVertInclLE d h y))
        = μ.real (boxConnEvent d n x y ∪ boxConnectionDetourEvent d h x y) := by
          rw [full_boxConnEvent_eq_inner_union_detour_of_le]
    _ ≤ μ.real (boxConnEvent d n x y) +
        μ.real (boxConnectionDetourEvent d h x y) :=
          measureReal_union_le _ _


theorem boxVertInclLE_range_iff
    (d : ℕ) {n N : ℕ} (h : n ≤ N) (z : boxVerts d N) :
    (∃ x : boxVerts d n, boxVertInclLE d h x = z) ↔
      (z : Lattice.Site d) ∈ Lattice.box d n := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hz
    exact ⟨⟨(z : Lattice.Site d), hz⟩, Subtype.ext rfl⟩


theorem openSub_boxRestrict_adj_boxVertInclLE
    (d : ℕ) {n N : ℕ} (h : n ≤ N)
    (ω : ConfigSpace (Sym2 (Lattice.Site d))) (x y : boxVerts d n) :
    (openSub (boxGraph d N) (boxRestrict d N ω)).Adj
        (boxVertInclLE d h x) (boxVertInclLE d h y)
      ↔ (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
  rw [openSub_adj, openSub_adj]
  have hadj :
      (boxGraph d N).Adj (boxVertInclLE d h x) (boxVertInclLE d h y)
        ↔ (boxGraph d n).Adj x y := by
    simp [boxGraph, boxVertInclLE]
  have hedge :
      s(boxVertInclLE d h x, boxVertInclLE d h y) = innerEdgeLE d h s(x, y) := by
    rw [innerEdgeLE, Sym2.map_mk]
  have hopen :
      boxRestrict d N ω s(boxVertInclLE d h x, boxVertInclLE d h y) =
        boxRestrict d n ω s(x, y) := by
    rw [hedge]
    exact congrFun (boxRestrictLE_boxRestrict d h ω) s(x, y)
  constructor
  · intro hxy
    exact ⟨hadj.mp hxy.1, by simpa [hopen] using hxy.2⟩
  · intro hxy
    exact ⟨hadj.mpr hxy.1, by simpa [hopen] using hxy.2⟩


theorem boxBoundary_of_openSub_adj_outer_of_le
    (d : ℕ) {n N : ℕ} (hn : 1 ≤ n) (h : n ≤ N)
    (ω : ConfigSpace (Sym2 (Lattice.Site d)))
    {x : boxVerts d n} {z : boxVerts d N}
    (hz : (z : Lattice.Site d) ∉ Lattice.box d n)
    (hadj : (openSub (boxGraph d N) (boxRestrict d N ω)).Adj
      (boxVertInclLE d h x) z) :
    boxBoundary d n x := by
  rw [openSub_adj] at hadj
  have hnn : Lattice.NearestNeighbour d (x : Lattice.Site d) (z : Lattice.Site d) := by
    have hcp := hadj.1
    rw [boxGraph, SimpleGraph.comap_adj] at hcp
    exact hcp
  exact ⟨x.2, notMem_box_pred_of_adj_outer hn x.2 hnn hz⟩


theorem connToBdry_of_outer_reachable_not_inner_of_le
    (d : ℕ) {n N : ℕ} (hn : 1 ≤ n) (h : n ≤ N)
    (ω : ConfigSpace (Sym2 (Lattice.Site d))) (y : boxVerts d n)
    (houter : (openSub (boxGraph d N) (boxRestrict d N ω)).Reachable
      (boxVertInclLE d h (IsingFK.boxOrigin d n)) (boxVertInclLE d h y))
    (hnotInner : ¬ (openSub (boxGraph d n) (boxRestrict d n ω)).Reachable
      (IsingFK.boxOrigin d n) y) :
    IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω)
      (IsingFK.boxOrigin d n) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at houter
  set OS := openSub (boxGraph d N) (boxRestrict d N ω)
  set os := openSub (boxGraph d n) (boxRestrict d n ω)
  suffices H : ∀ w : boxVerts d N,
      Relation.ReflTransGen OS.Adj (boxVertInclLE d h (IsingFK.boxOrigin d n)) w →
      (IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω)
          (IsingFK.boxOrigin d n)
        ∨ ∃ x : boxVerts d n, boxVertInclLE d h x = w
            ∧ os.Reachable (IsingFK.boxOrigin d n) x) by
    rcases H (boxVertInclLE d h y) houter with hdone | ⟨x, hx, hreach⟩
    · exact hdone
    · have hxy : x = y := by
        apply Subtype.ext
        have := congrArg Subtype.val hx
        simpa [boxVertInclLE] using this
      exact False.elim (hnotInner (by simpa [hxy] using hreach))
  intro w hw
  induction hw with
  | refl =>
      exact Or.inr
        ⟨IsingFK.boxOrigin d n, rfl, SimpleGraph.Reachable.refl _⟩
  | @tail u w hru hadj ih =>
      rcases ih with hdone | ⟨x, hx, hreach⟩
      · exact Or.inl hdone
      · subst hx
        by_cases hwinner : (w : Lattice.Site d) ∈ Lattice.box d n
        · let x' : boxVerts d n := ⟨(w : Lattice.Site d), hwinner⟩
          have hx' : boxVertInclLE d h x' = w := Subtype.ext rfl
          have hadj' : OS.Adj (boxVertInclLE d h x) (boxVertInclLE d h x') := by
            rwa [hx']
          exact Or.inr
            ⟨x', hx',
              hreach.trans
                ((openSub_boxRestrict_adj_boxVertInclLE d h ω x x').mp
                  (by simpa [OS, os] using hadj')).reachable⟩
        · exact Or.inl
            ⟨x, boxBoundary_of_openSub_adj_outer_of_le d hn h ω hwinner
              (by simpa [OS] using hadj), hreach⟩


theorem boxConnectionDetourEvent_subset_boxBdryConnEvent_of_le
    (d : ℕ) {n N : ℕ} (hn : 1 ≤ n) (h : n ≤ N) (y : boxVerts d n) :
    boxConnectionDetourEvent d h (IsingFK.boxOrigin d n) y ⊆
      boxBdryConnEvent d n := by
  intro ω hω
  rcases hω with ⟨houter, hnotInner⟩
  rw [boxConnEvent, Set.mem_preimage, connEvent] at houter hnotInner
  rw [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq]
  exact connToBdry_of_outer_reachable_not_inner_of_le d hn h ω y houter hnotInner


theorem boxConnectionDetourEvent_subset_boxBdryConnEvent_xaxis
    {n N : ℕ} (hn : 1 ≤ n) (h : n ≤ N) :
    boxConnectionDetourEvent 3 h
        (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)
      ⊆ boxBdryConnEvent 3 n := by
  have horigin : ising3DOriginBoxVertex n = IsingFK.boxOrigin 3 n := by
    ext
    rfl
  simpa [horigin] using
    boxConnectionDetourEvent_subset_boxBdryConnEvent_of_le
      3 hn h (ising3DXAxisBoxVertex n)


theorem freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full_of_le
    (β : ℝ) (hβ : 0 < β) {N n : ℕ} (hn : n ≤ N) :
    freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n ≤
      freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n := by
  unfold freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
    freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume
  rw [dif_pos hn]
  exact measureReal_mono
    (boxConnEvent_subset_full_boxConnEvent_of_le 3 hn
      (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n))


theorem eventually_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full
    (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    ∀ᶠ N in atTop,
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n ≤
        freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n := by
  filter_upwards [eventually_ge_atTop n] with N hN
  exact freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full_of_le β hβ hN


end Exact3D
end StatMech
