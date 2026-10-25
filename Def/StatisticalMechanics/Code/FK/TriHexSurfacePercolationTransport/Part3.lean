/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusBoundaryReach
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationClosure
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationTransport.Part2
open Filter Finset MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

def TriangularTorusRadialPercolates (p q : Real) : Prop :=
  ∃ theta : Real,
    Tendsto (triangularTorusRadialReachProbability p q) atTop (nhds theta) ∧
      0 < theta


def HexagonalTorusRadialPercolates (p q : Real) : Prop :=
  ∃ theta : Real,
    Tendsto (hexagonalTorusRadialReachProbability p q) atTop (nhds theta) ∧
      0 < theta


end
end StatMech.FK.PeriodicPlanar
