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
import Def.StatisticalMechanics.Code.OSSS.WiredBoxDifferential.Part3
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace WiredBoxDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open ActiveBoundaryDifferential

open FK RevealmentTranslation


@[simp] theorem mem_osssBoundaryFinset {d n : Nat} {x : Site d} :
    x ∈ osssBoundaryFinset d n <-> x ∈ vertexBoundary d n := by
  rw [osssBoundaryFinset, Set.Finite.mem_toFinset]

theorem origin_mem_osssBoxFinset (d n : Nat) :
    (0 : Site d) ∈ osssBoxFinset d n := by
  rw [mem_osssBoxFinset]
  intro i
  simp

theorem origin_not_mem_osssBoundaryFinset (d k : Nat) :
    (0 : Site d) ∉ osssBoundaryFinset d k := by
  rw [mem_osssBoundaryFinset]
  intro h
  exact h.2 (by intro i; simp)

theorem boxActiveEndU_mem (d n : Nat) (e : (boxGraph d n).edgeSet) :
    boxActiveEndU d n e ∈ osssBoxFinset d n := by
  rw [mem_osssBoxFinset]
  exact e.1.out.1.property

theorem boxActiveEndV_mem (d n : Nat) (e : (boxGraph d n).edgeSet) :
    boxActiveEndV d n e ∈ osssBoxFinset d n := by
  rw [mem_osssBoxFinset]
  exact e.1.out.2.property


end WiredBoxDifferential
end OSSS
end StatMech
