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
import Def.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part3
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


theorem freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary_of_le
    (β : ℝ) (hβ : 0 < β) {N n : ℕ} (hnpos : 1 ≤ n) (hn : n ≤ N) :
    freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n ≤
      freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβ N n := by
  unfold freeFiniteVolumeXAxisDetourOfBetaQ2InVolume
    freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume
  rw [dif_pos hn]
  exact measureReal_mono
    (boxConnectionDetourEvent_subset_boxBdryConnEvent_xaxis hnpos hn)


theorem eventually_freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary
    (β : ℝ) (hβ : 0 < β) (n : ℕ) (hnpos : 1 ≤ n) :
    ∀ᶠ N in atTop,
      freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n ≤
        freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβ N n := by
  filter_upwards [eventually_ge_atTop n] with N hN
  exact freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary_of_le
    β hβ hnpos hN


theorem freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour_of_le
    (β : ℝ) (hβ : 0 < β) {N n : ℕ} (hn : n ≤ N) :
    freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n ≤
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n +
        freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n := by
  unfold freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume
    freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
    freeFiniteVolumeXAxisDetourOfBetaQ2InVolume
  rw [dif_pos hn, dif_pos hn]
  have horigin :
      boxVertInclLE 3 hn (ising3DOriginBoxVertex n) =
        ising3DOriginBoxVertex N := by
    ext
    rfl
  have hxaxis :
      boxVertInclLE 3 hn (ising3DXAxisBoxVertex n) =
        ising3DXAxisBoxVertexInBox N n hn := by
    ext
    rfl
  simpa [horigin, hxaxis] using
    measureReal_full_boxConnEvent_le_inner_add_detour
    (d := 3)
    (μ := (freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ)
      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))))
    hn
    (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)


theorem eventually_freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour
    (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    ∀ᶠ N in atTop,
      freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n ≤
        freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n +
          freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n := by
  filter_upwards [eventually_ge_atTop n] with N hN
  exact
    freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour_of_le
      β hβ hN


theorem wiredFiniteMeasure_boxConnEvent_tendsto_wiredInfiniteVolume_q2
    (d N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N) :
    Tendsto (fun m =>
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y))
      atTop
      (nhds ((wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y))) := by
  simpa [boxConnEvent] using
    (fk_wired_infinite_measure (d := d) N hp hp1
      (S := connEvent (boxGraph d N) x y)
      (connEvent_isIncreasing (boxGraph d N) x y))


theorem freeInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2
    (d N : ℕ) {p B : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N)
    (hB :
      ∀ᶠ m in atTop,
        (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
            (boxConnEvent d N x y) ≤ B) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d N x y) ≤ B := by
  exact le_of_tendsto
    (freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2
      d N hp hp1 x y) hB


theorem le_freeInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2
    (d N : ℕ) {p B : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N)
    (hB :
      ∀ᶠ m in atTop,
        B ≤ (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
            (boxConnEvent d N x y)) :
    B ≤ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d N x y) := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (freeFiniteMeasure_boxConnEvent_tendsto_freeInfiniteVolume_q2
      d N hp hp1 x y) hB


theorem wiredInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2
    (d N : ℕ) {p B : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N)
    (hB :
      ∀ᶠ m in atTop,
        (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
            (boxConnEvent d N x y) ≤ B) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d N x y) ≤ B := by
  exact le_of_tendsto
    (wiredFiniteMeasure_boxConnEvent_tendsto_wiredInfiniteVolume_q2
      d N hp hp1 x y) hB


theorem le_wiredInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2
    (d N : ℕ) {p B : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : boxVerts d N)
    (hB :
      ∀ᶠ m in atTop,
        B ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
            (boxConnEvent d N x y)) :
    B ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxConnEvent d N x y) := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (wiredFiniteMeasure_boxConnEvent_tendsto_wiredInfiniteVolume_q2
      d N hp hp1 x y) hB


theorem freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
    {p B : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ)
    (hB :
      ∀ᶠ m in atTop,
        (freeFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) ≤ B) :
    freeInfiniteVolumeXAxisConnectionQ2 p hp hp1 n ≤ B := by
  simpa [freeInfiniteVolumeXAxisConnectionQ2] using
    freeInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2
      3 n hp hp1 (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n) hB


theorem le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
    {p B : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ)
    (hB :
      ∀ᶠ m in atTop,
        B ≤ (freeFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n))) :
    B ≤ freeInfiniteVolumeXAxisConnectionQ2 p hp hp1 n := by
  simpa [freeInfiniteVolumeXAxisConnectionQ2] using
    le_freeInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2
      3 n hp hp1 (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n) hB


theorem wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
    {p B : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ)
    (hB :
      ∀ᶠ m in atTop,
        (wiredFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) ≤ B) :
    wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1 n ≤ B := by
  simpa [wiredInfiniteVolumeXAxisConnectionQ2] using
    wiredInfiniteVolume_boxConnEvent_le_of_eventually_finiteVolume_le_q2
      3 n hp hp1 (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n) hB


theorem le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
    {p B : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ)
    (hB :
      ∀ᶠ m in atTop,
        B ≤ (wiredFiniteMeasure 3 m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n))) :
    B ≤ wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1 n := by
  simpa [wiredInfiniteVolumeXAxisConnectionQ2] using
    le_wiredInfiniteVolume_boxConnEvent_of_eventually_le_finiteVolume_q2
      3 n hp hp1 (ising3DOriginBoxVertex n)
      (ising3DXAxisBoxVertex n) hB


theorem
    fkTwoSidedFreeIVQ2_of_eventually_boxConnEvent_bounds
    {p mass : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {Alo Ahi : ℕ → ℝ}
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (boxConnEvent 3 n (ising3DOriginBoxVertex n)
                (ising3DXAxisBoxVertex n)))
    (hhi :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeInfiniteVolumeXAxisConnectionQ2 p hp hp1) Alo Ahi mass := by
  refine ⟨hlo_pos, hhi_pos, hlo_log, hhi_log, ?_, ?_⟩
  · filter_upwards [hlo] with n hn
    exact le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n hn
  · filter_upwards [hhi] with n hn
    exact freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n hn


theorem
    fkTwoSidedWiredIVQ2_of_eventually_boxConnEvent_bounds
    {p mass : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {Alo Ahi : ℕ → ℝ}
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (boxConnEvent 3 n (ising3DOriginBoxVertex n)
                (ising3DXAxisBoxVertex n)))
    (hhi :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1) Alo Ahi mass := by
  refine ⟨hlo_pos, hhi_pos, hlo_log, hhi_log, ?_, ?_⟩
  · filter_upwards [hlo] with n hn
    exact le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n hn
  · filter_upwards [hhi] with n hn
    exact wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n hn


theorem fkExactFreeIVQ2_of_eventually_boxConnEvent_eq
    {p A mass : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (h :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) =
          A * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionExactExponentialDecay
      (freeInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
  filter_upwards [h] with n hn
  exact le_antisymm
    (freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM))
    (le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM.symm))


theorem fkExactWiredIVQ2_of_eventually_boxConnEvent_eq
    {p A mass : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (h :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) =
          A * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionExactExponentialDecay
      (wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
  filter_upwards [h] with n hn
  exact le_antisymm
    (wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM))
    (le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM.symm))


theorem fkSubexpFreeIVQ2_of_eventually_boxConnEvent_eq
    {p mass : ℝ} (hp : 0 < p) (hp1 : p < 1) {A : ℕ → ℝ}
    (hA_pos : ∀ᶠ n in atTop, 0 < A n)
    (hA_log :
      Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
        atTop (nhds 0))
    (h :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (freeFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) =
          A n * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
  refine ⟨hA_pos, hA_log, ?_⟩
  filter_upwards [h] with n hn
  exact le_antisymm
    (freeInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM))
    (le_freeInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM.symm))


theorem fkSubexpWiredIVQ2_of_eventually_boxConnEvent_eq
    {p mass : ℝ} (hp : 0 < p) (hp1 : p < 1) {A : ℕ → ℝ}
    (hA_pos : ∀ᶠ n in atTop, 0 < A n)
    (hA_log :
      Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
        atTop (nhds 0))
    (h :
      ∀ᶠ n in atTop, ∀ᶠ M in atTop,
        (wiredFiniteMeasure 3 M hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (boxConnEvent 3 n (ising3DOriginBoxVertex n)
              (ising3DXAxisBoxVertex n)) =
          A n * Real.exp (-(mass * (n : ℝ)))) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (wiredInfiniteVolumeXAxisConnectionQ2 p hp hp1) A mass := by
  refine ⟨hA_pos, hA_log, ?_⟩
  filter_upwards [h] with n hn
  exact le_antisymm
    (wiredInfiniteVolumeXAxisConnectionQ2_le_of_eventually_boxConnEvent_le
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM))
    (le_wiredInfiniteVolumeXAxisConnectionQ2_of_eventually_le_boxConnEvent
      hp hp1 n (hn.mono fun _ hM => le_of_eq hM.symm))


end Exact3D
end StatMech
