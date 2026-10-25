/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part3
open Filter MeasureTheory Set SimpleGraph Topology Finset
open scoped ENNReal BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice StatMech.FrontierA

variable {V : Type*} [Countable V] [DecidableEq V]


noncomputable def PeriodicGraph.orbitShell
    (P : PeriodicGraph V) (n c : Nat) : Finset V :=
  P.orbitBox (n + c) \ P.orbitBox n

noncomputable def PeriodicGraph.orbitShellSource
    (P : PeriodicGraph V) (n c : Nat) : Finset (Site 2 × V) :=
  ((box_finite 2 (n + c)).toFinset \ (box_finite 2 n).toFinset) ×ˢ
    P.fundamentalDomain

end StatMech.FK.PeriodicPlanar
