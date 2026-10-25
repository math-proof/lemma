/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part7
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


noncomputable def PeriodicGraph.rootedOpenPathEvent
    (P : PeriodicGraph V) (n : Nat) : Set (ConfigSpace (Sym2 V)) := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  exact StatMech.FK.PeriodicPlanar.rootedOpenPathEvent P.graph P.root n


end StatMech.FK.PeriodicPlanar
