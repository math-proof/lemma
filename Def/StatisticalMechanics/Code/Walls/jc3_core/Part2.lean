module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.jc2_core.Part3
public import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc2_thinthickdichotomy.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc2_thinconn
public import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
public import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
public import Theorem.StatisticalMechanics.Code.Walls.jc3_clipsymmdiff
public import Theorem.StatisticalMechanics.Code.Walls.jc3_shelfcell
public import Theorem.StatisticalMechanics.Code.Walls.jc3_tailturneq
public import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
public import Theorem.StatisticalMechanics.Code.Walls.jc3_core
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc3_SaturatingOrbitSplice : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      K ⊆ bpc_orbitFootprint K a →
      ∀ c len, jc2_RunFrame K c len → jc3_OrbitSpliceDatum K a (c + ![len, 0])


end Walls
end StatMech
