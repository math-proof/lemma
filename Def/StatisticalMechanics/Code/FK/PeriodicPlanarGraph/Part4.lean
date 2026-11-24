module
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part2
open Finset Set SimpleGraph
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


def PeriodicGraph.orbitBoundary (P : PeriodicGraph V) (n : ℕ)
    (v : P.OrbitVertex n) : Prop :=
  (v : V) ∉ P.orbitBox (n - 1)

end PeriodicPlanar
end FK
end StatMech
