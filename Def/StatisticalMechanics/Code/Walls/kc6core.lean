module
public import Theorem.StatisticalMechanics.Code.Walls.kc5_core.Part2
public import Theorem.StatisticalMechanics.Code.Walls.kc6evenoddrule
public import Theorem.StatisticalMechanics.Code.Walls.kc6uniqueinfinitecomponent
public import Theorem.StatisticalMechanics.Code.Walls.kc6cornercellodd
public import Theorem.StatisticalMechanics.Code.Walls.kc6windingwitness
public import Theorem.StatisticalMechanics.Code.Walls.kc3_core
public import Theorem.StatisticalMechanics.Code.Walls.kc3_oddrayeqleftRegion.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WindingWitnessClose
public import Theorem.StatisticalMechanics.Code.Walls.kc6core
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def kc6_OffSupportOutsideInK (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z, z ∉ K → z ∉ (mpl_orbitLoop K a).support → z ∉ jec_leftRegion (mpl_orbitLoop K a)


end Walls
end StatMech
