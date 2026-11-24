module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
public import Theorem.StatisticalMechanics.Code.Walls.kc2_core.Part3
public import Theorem.StatisticalMechanics.Code.Walls.kc3_oddrayeqleftRegion
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_oddrayeqleftRegion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def kc3_LeftRegionSupportSubset (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  jec_leftRegion (mpl_orbitLoop K a) ∩ {z | z ∈ (mpl_orbitLoop K a).support} ⊆ K


end Walls
end StatMech
