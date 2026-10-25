/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneCore.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge.Part2
open MeasureTheory Set SimpleGraph
open scoped ENNReal


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]

def PeriodicGraph.distinctInfinitePairEvent
    (P : PeriodicGraph V) (x y : V) : Set (ConfigSpace (Sym2 V)) :=
  {omega | (P.cluster omega x).Infinite ∧
    (P.cluster omega y).Infinite ∧
      P.cluster omega x ≠ P.cluster omega y}

end StatMech.FK.PeriodicPlanar
