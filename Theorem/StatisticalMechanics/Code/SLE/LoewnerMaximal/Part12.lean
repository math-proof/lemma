/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part11
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem loewnerMaximalMaps_flow
    {W : ℝ → ℝ} {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W (s + u)) :
    loewnerMaximalMaps W (s + u) z =
      loewnerMaximalMaps (fun r ↦ W (s + r)) u (loewnerMaximalMaps W s z) := by
  let g := selectedLoewnerSolution hz.2
  have hT : 0 < selectedLoewnerDuration hz.2 :=
    (selectedLoewnerDuration_spec hz.2).1.1
  have hsuT : s + u < selectedLoewnerDuration hz.2 :=
    (selectedLoewnerDuration_spec hz.2).2
  simpa only [loewnerMaximalMaps] using
    loewnerMaximalCurve_flow_of_forwardSolution hT g hs hu hsuT


theorem loewnerMaximalMaps_mem_shiftedUnswallowedDomain
    {W : ℝ → ℝ} {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W (s + u)) :
    loewnerMaximalMaps W s z ∈
      loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := by
  let g := selectedLoewnerSolution hz.2
  let T := selectedLoewnerDuration hz.2
  have hT : 0 < T := (selectedLoewnerDuration_spec hz.2).1.1
  have hsuT : s + u < T := (selectedLoewnerDuration_spec hz.2).2
  have hsT : s < T := lt_of_le_of_lt (le_add_of_nonneg_right hu) hsuT
  let h := g.timeShift s hs
  have hshiftT : 0 < T - s := sub_pos.mpr hsT
  have hbefore : IsBeforeLoewnerLifetime (fun r ↦ W (s + r)) (g.curve s) u :=
    (isBeforeLoewnerLifetime_iff_exists_admissible hu).2
      ⟨T - s, ⟨hshiftT, ⟨h⟩⟩, by linarith⟩
  change loewnerMaximalCurve W z s ∈
    loewnerUnswallowedDomain (fun r ↦ W (s + r)) u
  rw [loewnerMaximalCurve_eq_forwardSolution hT g ⟨hs, hsT⟩]
  exact ⟨g.upper s ⟨hs, hsT.le⟩, hbefore⟩


theorem mem_loewnerUnswallowedDomain_zero {W : ℝ → ℝ} (hW : Continuous W)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : z ∈ loewnerUnswallowedDomain W 0 := by
  refine ⟨hz, le_rfl, ?_⟩
  simpa using loewnerLifetime_pos hW (mem_upperHalfPlane.mp hz)


theorem loewnerMaximalMaps_zero {W : ℝ → ℝ} (hW : Continuous W)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : loewnerMaximalMaps W 0 z = z :=
  loewnerMaximalCurve_zero hW (mem_upperHalfPlane.mp hz)


theorem loewnerMaximalMaps_mem_upperHalfPlane {W : ℝ → ℝ} {t : ℝ} {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    loewnerMaximalMaps W t z ∈ upperHalfPlane :=
  loewnerMaximalCurve_mem_upperHalfPlane hz.2


theorem loewnerMaximalMaps_hasDerivAt {W : ℝ → ℝ} {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    HasDerivAt (fun s ↦ loewnerMaximalMaps W s z)
      (loewnerField W t (loewnerMaximalMaps W t z)) t :=
  loewnerMaximalCurve_hasDerivAt ht hz.2.2


theorem loewnerMaximalMaps_hasDerivWithinAt_zero {W : ℝ → ℝ} (hW : Continuous W)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivWithinAt (fun s ↦ loewnerMaximalMaps W s z)
      (loewnerField W 0 (loewnerMaximalMaps W 0 z)) (Ici (0 : ℝ)) 0 :=
  loewnerMaximalCurve_hasDerivWithinAt_zero hW (mem_upperHalfPlane.mp hz)


theorem loewnerMaximalMaps_injOn {W : ℝ → ℝ} (hW : Continuous W)
    {t : ℝ} (ht : 0 ≤ t) :
    InjOn (loewnerMaximalMaps W t) (loewnerUnswallowedDomain W t) := by
  rcases ht.eq_or_lt with rfl | ht0
  · intro z hz w hw heq
    calc
      z = loewnerMaximalMaps W 0 z := (loewnerMaximalMaps_zero hW hz.1).symm
      _ = loewnerMaximalMaps W 0 w := heq
      _ = w := loewnerMaximalMaps_zero hW hw.1
  · intro z hz w hw heq
    let g := selectedLoewnerSolution hz.2
    let h := selectedLoewnerSolution hw.2
    have hS : 0 < selectedLoewnerDuration hz.2 :=
      (selectedLoewnerDuration_spec hz.2).1.1
    have hT : 0 < selectedLoewnerDuration hw.2 :=
      (selectedLoewnerDuration_spec hw.2).1.1
    have htS : t < selectedLoewnerDuration hz.2 :=
      (selectedLoewnerDuration_spec hz.2).2
    have htT : t < selectedLoewnerDuration hw.2 :=
      (selectedLoewnerDuration_spec hw.2).2
    have hcurve : g.curve t = h.curve t := by
      rw [← loewnerMaximalCurve_eq_forwardSolution hS g ⟨ht0.le, htS⟩,
        ← loewnerMaximalCurve_eq_forwardSolution hT h ⟨ht0.le, htT⟩]
      exact heq
    exact g.initial_eq_of_eq_at hS hT h ht0 htS htT hcurve


theorem loewnerMaximalMaps_surjOn_upperHalfPlane
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    SurjOn (loewnerMaximalMaps W t)
      (loewnerUnswallowedDomain W t) upperHalfPlane := by
  intro y hyUpper
  have hy : 0 < y.im := mem_upperHalfPlane.mp hyUpper
  obtain ⟨x, g, hgEnd⟩ := exists_loewnerBackwardSolution hW ht hy
  have hWt : Continuous (fun u ↦ W (t + u)) :=
    hW.comp (continuous_const.add continuous_id)
  obtain ⟨E, hE, h, hh0, hhd, hhu⟩ :=
    loewner_local_existence hWt hy
  let h' : LoewnerForwardSolution (fun u ↦ W (t + u)) (g.curve t) E :=
    { curve := h
      initial := hh0.trans hgEnd.symm
      deriv := hhd
      upper := hhu }
  let gh : LoewnerForwardSolution W x (t + E) :=
    g.append h' ht hE.le
  have htotal : 0 < t + E := by linarith
  have hxUpper : x ∈ upperHalfPlane := by
    rw [← g.initial]
    exact g.upper 0 ⟨le_rfl, ht⟩
  have hbefore : IsBeforeLoewnerLifetime W x t :=
    (isBeforeLoewnerLifetime_iff_exists_admissible ht).2
      ⟨t + E, ⟨htotal, ⟨gh⟩⟩, by linarith⟩
  have ghAt : gh.curve t = y := by
    simp [gh, LoewnerForwardSolution.append,
      LoewnerForwardSolution.appendCurve, hgEnd]
  refine ⟨x, ⟨hxUpper, hbefore⟩, ?_⟩
  calc
    loewnerMaximalMaps W t x = gh.curve t := by
      exact loewnerMaximalCurve_eq_forwardSolution htotal gh ⟨ht, by linarith⟩
    _ = y := ghAt


theorem loewnerMaximalMaps_bijOn_upperHalfPlane
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    BijOn (loewnerMaximalMaps W t)
      (loewnerUnswallowedDomain W t) upperHalfPlane := by
  refine ⟨?_, loewnerMaximalMaps_injOn hW ht,
    loewnerMaximalMaps_surjOn_upperHalfPlane hW ht⟩
  intro z hz
  exact loewnerMaximalMaps_mem_upperHalfPlane hz


end StatMech.SLE
