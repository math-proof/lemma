/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part3
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


noncomputable def PeriodicGraph.extendEdge (P : PeriodicGraph V) (n : ℕ)
    (omega : ConfigSpace (Sym2 (P.OrbitVertex n))) : ConfigSpace (Sym2 V) :=
  fun e => if h : e ∈ Set.range (P.edgeIncl n) then omega h.choose else false

end PeriodicPlanar
end FK
end StatMech
