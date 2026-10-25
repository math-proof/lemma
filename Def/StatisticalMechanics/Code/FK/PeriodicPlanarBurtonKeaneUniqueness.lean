/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeanePattern.Part2
open MeasureTheory Set SimpleGraph
open scoped ENNReal


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type} [Countable V] [DecidableEq V]

def PeriodicGraph.threeDistinctInfiniteEvent (P : PeriodicGraph V)
    (x : Fin 3 → V) : Set (ConfigSpace (Sym2 V)) :=
  {omega | (∀ i, (P.cluster omega (x i)).Infinite) ∧
    ∀ i j, i ≠ j → P.cluster omega (x i) ≠ P.cluster omega (x j)}

end StatMech.FK.PeriodicPlanar
