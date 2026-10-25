/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


def PeriodicGraph.shiftIso (P : PeriodicGraph V) (z : Lattice.Site 2) :
    P.graph ≃g P.graph where
  toEquiv := P.shift z
  map_rel_iff' := fun {x y} => P.shift_adj z x y


noncomputable def PeriodicGraph.vertexDegree (P : PeriodicGraph V) (v : V) : Nat :=
  @SimpleGraph.degree V P.graph v (P.locallyFinite v)

end StatMech.FK.PeriodicPlanar
