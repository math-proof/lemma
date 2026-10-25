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
import Def.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part6
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

theorem zih_rot_dependsOn {A : Set (ConfigSpace (Sym2 (Site 2)))}
    {F : Finset (Sym2 (Site 2))} (hA : StatMech.DependsOn A F) :
    StatMech.DependsOn (zrs_rot A) (zih_rotSupport F) := by
  intro omega omega' hagree
  apply hA
  intro e he
  simp only [zrs_rot, Set.mem_preimage, zrs_rotConfig_apply]
  apply hagree
  rw [Finset.mem_coe, zih_rotSupport, Finset.mem_image]
  exact ⟨e, by simpa using he, rfl⟩

end StatMech.TwoDim
