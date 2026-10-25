/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part13
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem isConnected_loewnerUnswallowedDomain
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsConnected (loewnerUnswallowedDomain W t) := by
  have hH : IsConnected upperHalfPlane := by
    have h : upperHalfPlane = {c : ℂ | (0 : ℝ) < c.im} := rfl
    rw [h]
    exact (convex_halfSpace_im_gt 0).isConnected
      ⟨(0 + 1) * Complex.I, by simp⟩
  have himage := hH.image (loewnerMaximalMapsInverse hW ht)
    (continuousOn_loewnerMaximalMapsInverse hW ht)
  have heq : loewnerMaximalMapsInverse hW ht '' upperHalfPlane =
      loewnerUnswallowedDomain W t := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact loewnerMaximalMapsInverse_mem hW ht hy
    · intro x hx
      let y := loewnerMaximalMaps W t x
      have hy : y ∈ upperHalfPlane := loewnerMaximalMaps_mem_upperHalfPlane hx
      refine ⟨y, hy, ?_⟩
      exact (eq_loewnerMaximalMapsInverse_of_mapsTo hW ht hx hy rfl).symm
  rwa [heq] at himage


theorem isBeforeLoewnerLifetime_add_iff_shifted
    {W : ℝ → ℝ} {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) {z : ℂ}
    (hzs : z ∈ loewnerUnswallowedDomain W s) :
    IsBeforeLoewnerLifetime W z (s + u) ↔
      IsBeforeLoewnerLifetime (fun r ↦ W (s + r))
        (loewnerMaximalMaps W s z) u := by
  constructor
  · intro hz
    have hadd : z ∈ loewnerUnswallowedDomain W (s + u) := ⟨hzs.1, hz⟩
    have hrhs := (Set.ext_iff.mp (loewnerUnswallowedDomain_add_eq W hs hu) z).mp hadd
    exact hrhs.2.2
  · intro hz
    have hshift : loewnerMaximalMaps W s z ∈
        loewnerUnswallowedDomain (fun r ↦ W (s + r)) u :=
      ⟨loewnerMaximalMaps_mem_upperHalfPlane hzs, hz⟩
    have hrhs : z ∈ loewnerUnswallowedDomain W s ∩
        loewnerMaximalMaps W s ⁻¹'
          loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := ⟨hzs, hshift⟩
    exact ((Set.ext_iff.mp (loewnerUnswallowedDomain_add_eq W hs hu) z).mpr hrhs).2


end StatMech.SLE
