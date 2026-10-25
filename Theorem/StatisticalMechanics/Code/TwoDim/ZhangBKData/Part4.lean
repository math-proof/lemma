/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry.Part3
import Theorem.StatisticalMechanics.Code.Walls.binsclosure.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part3
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation StatMech.Walls


theorem zbd_sideHasInfinite_measurableSet {d : ℕ} (S : Set (Site d)) :
    MeasurableSet (zbd_sideHasInfinite S) := by
  have heq : zbd_sideHasInfinite S =
      ⋃ x : Site d, ⋃ (_hx : x ∈ S), {omega | (cluster d omega x).Infinite} := by
    ext omega
    simp [zbd_sideHasInfinite]
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  exact measurableSet_clusterInfinite x

theorem zbd_sideHasInfinite_isIncreasing {d : ℕ} (S : Set (Site d)) :
    IsIncreasing (zbd_sideHasInfinite S) := by
  intro omega omega' hle
  rintro ⟨x, hxS, hxinf⟩
  exact ⟨x, hxS, hxinf.mono (cluster_mono hle x)⟩


end StatMech.TwoDim
