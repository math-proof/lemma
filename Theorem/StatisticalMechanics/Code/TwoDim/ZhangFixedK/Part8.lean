module
public import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
public import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
public import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
public import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
public import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part8
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


@[simp] theorem zfk_mem_leftCentralFinset {k : ℕ} {x : Site 2} :
    x ∈ zfk_leftCentralFinset k ↔ x ∈ box 2 k := by
  rw [zfk_leftCentralFinset, Set.Finite.mem_toFinset]

@[simp] theorem zfk_mem_rightCentralFinset {k : ℕ} {x : Site 2} :
    x ∈ zfk_rightCentralFinset k ↔ x ∈ zfk_rightCentralBox k := by
  rw [zfk_rightCentralFinset, Set.Finite.mem_toFinset]


end StatMech.TwoDim
