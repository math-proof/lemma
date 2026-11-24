module
public import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
public import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
public import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
public import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
public import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part7
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


noncomputable def zfk_leftCentralFinset (k : ℕ) : Finset (Site 2) :=
  (box_finite 2 k).toFinset

noncomputable def zfk_rightCentralFinset (k : ℕ) : Finset (Site 2) :=
  (zfk_rightCentralBox_finite k).toFinset

end StatMech.TwoDim
