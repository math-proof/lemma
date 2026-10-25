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
import Def.StatisticalMechanics.Code.OSSS.WiredBoxDifferential
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace WiredBoxDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open ActiveBoundaryDifferential

open FK RevealmentTranslation


theorem boxActiveEdge_injective (d n : Nat) :
    Function.Injective (boxActiveEdge d n) := by
  intro e f h
  apply Subtype.ext
  exact edgeIncl_injective d n h

theorem boxActiveEdge_eq_endpoints (d n : Nat)
    (e : (boxGraph d n).edgeSet) :
    boxActiveEdge d n e = s(boxActiveEndU d n e, boxActiveEndV d n e) := by
  change edgeIncl d n e.1 =
    s(((e.1.out.1 : boxVerts d n) : Site d),
      ((e.1.out.2 : boxVerts d n) : Site d))
  calc
    edgeIncl d n e.1 = edgeIncl d n s(e.1.out.1, e.1.out.2) :=
      congrArg (edgeIncl d n) e.1.out_eq.symm
    _ = s(((e.1.out.1 : boxVerts d n) : Site d),
        ((e.1.out.2 : boxVerts d n) : Site d)) := by
      rw [edgeIncl, Sym2.map_mk]

theorem boxActiveEnd_adj (d n : Nat) (e : (boxGraph d n).edgeSet) :
    (hypercubicLattice d).Adj (boxActiveEndU d n e) (boxActiveEndV d n e) := by
  have he : (boxGraph d n).Adj e.1.out.1 e.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
    rw [hout]
    exact e.2
  exact he


end WiredBoxDifferential
end OSSS
end StatMech
