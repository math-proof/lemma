/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part2
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


def zfk_rightCentralBox (k : ℕ) : Set (Site 2) :=
  {x | x - ![1, 0] ∈ box 2 k}


def zfk_leftSquare (N : ℕ) : Set (Site 2) :=
  rect (-(N : ℤ)) N (-(N : ℤ)) N


def zfk_rightSquare (N : ℕ) : Set (Site 2) :=
  rect (-(N : ℤ) + 1) (N + 1) (-(N : ℤ)) N

end StatMech.TwoDim
