module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc4_tailnotprobed
public import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc5_footprintdartsfinite
public import Theorem.StatisticalMechanics.Code.Walls.jc6_ivt.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc7ivtnohop
public import Theorem.StatisticalMechanics.Code.Walls.jc7getverteqdartface
public import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
public import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc7stepfacebridge
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Walls.jc7core
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc7_SinglePass (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) : Prop :=
  ∀ i j k, i < j → j < k → ¬ jc4_FootprintFree K a r i → ¬ jc4_FootprintFree K a r k →
    ¬ jc4_FootprintFree K a r j


end Walls
end StatMech
