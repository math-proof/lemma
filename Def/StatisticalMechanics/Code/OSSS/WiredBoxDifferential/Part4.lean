module
public import Theorem.StatisticalMechanics.Code.OSSS.ActiveBoundaryDifferential
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxDifferential.Part3
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


noncomputable def wiredBoxBoundaryGraph (d n : Nat) :
    SimpleGraph (boxVerts d n) :=
  Lattice.boundaryCliqueGraph (boxBoundary d n)

end WiredBoxDifferential
end OSSS
end StatMech
