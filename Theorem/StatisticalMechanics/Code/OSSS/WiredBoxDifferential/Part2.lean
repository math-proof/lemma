module
public import Theorem.StatisticalMechanics.Code.OSSS.ActiveBoundaryDifferential
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Def.StatisticalMechanics.Code.OSSS.WiredBoxDifferential.Part2
open scoped BigOperators Classical
open Finset Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace OSSS

namespace WiredBoxDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open ActiveBoundaryDifferential

open FK RevealmentTranslation


@[simp] theorem mem_osssBoxFinset {d n : Nat} {x : Site d} :
    x ∈ osssBoxFinset d n <-> x ∈ box d n := by
  rw [osssBoxFinset, Set.Finite.mem_toFinset]


end WiredBoxDifferential
end OSSS
end StatMech
