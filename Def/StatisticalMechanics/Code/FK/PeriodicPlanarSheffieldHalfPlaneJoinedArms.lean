/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneInfiniteArm
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneStripUnion
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def walkOfChain (G : SimpleGraph V) (x : V) :
    (l : List V) → List.IsChain G.Adj (x :: l) →
      G.Walk x ((x :: l).getLast (List.cons_ne_nil _ _))
  | [], _ => .nil
  | y :: l, h => by
      have h' : G.Adj x y ∧ List.IsChain G.Adj (y :: l) := by
        simpa only [List.isChain_cons_cons] using h
      exact .cons h'.1 (walkOfChain G y l h'.2)

end StatMech.FK.PeriodicPlanar
