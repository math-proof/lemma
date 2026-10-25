/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeanePattern.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ThreePendantTree
import Theorem.StatisticalMechanics.Code.Percolation.TreeExteriorAmalgam
open MeasureTheory Set SimpleGraph Finset


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type} [Countable V] [DecidableEq V]

noncomputable def PeriodicGraph.incidentEdgeFinset
    (P : PeriodicGraph V) (K : Finset V) : Finset (Sym2 V) := by
  letI : P.graph.LocallyFinite := P.locallyFinite
  exact K.biUnion fun x => (P.graph.neighborFinset x).image fun y => s(x, y)

end StatMech.FK.PeriodicPlanar
