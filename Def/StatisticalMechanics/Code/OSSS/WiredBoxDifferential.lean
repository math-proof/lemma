/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ActiveBoundaryDifferential
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace WiredBoxDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open ActiveBoundaryDifferential

open FK RevealmentTranslation


def boxActiveEdge (d n : Nat) :
    (boxGraph d n).edgeSet -> Sym2 (Site d) :=
  fun e => edgeIncl d n e.1


noncomputable def boxActiveEndU (d n : Nat) :
    (boxGraph d n).edgeSet -> Site d :=
  fun e => (e.1.out.1 : boxVerts d n)


noncomputable def boxActiveEndV (d n : Nat) :
    (boxGraph d n).edgeSet -> Site d :=
  fun e => (e.1.out.2 : boxVerts d n)

end WiredBoxDifferential
end OSSS
end StatMech
