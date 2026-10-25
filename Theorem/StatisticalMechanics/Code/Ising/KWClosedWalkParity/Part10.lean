/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Def.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part7
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section RegionSide

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


omit [DecidableEq V] in


theorem mem_regionBoundary_iff (S : V → Bool) {u v : V} (h : Gp.Adj u v) :
    s(u, v) ∈ regionBoundary Gp S ↔ S u ≠ S v :=
  cutEdges_isCoboundary S h


theorem evenOnCycles_regionBoundary (S : V → Bool) :
    EvenOnCycles Gp (regionBoundary Gp S) :=
  evenOnCycles_of_isCoboundary S (fun h => mem_regionBoundary_iff S h)


end RegionSide
end Ising
end StatMech
