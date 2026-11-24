module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
public import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
public import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part3
open MeasureTheory Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC FrontierA

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


def TriangularCriticalPhaseBoundary (q pc : ℝ) : Prop :=
  CriticalSurfacePhaseBoundary
    (fun p => triangularFKCriticalPolynomial q (fkEdgeOdds p)) pc


def HexagonalCriticalPhaseBoundary (q pc : ℝ) : Prop :=
  CriticalSurfacePhaseBoundary
    (fun p => hexagonalFKCriticalPolynomial q (fkEdgeOdds p)) pc

end PeriodicPlanar
end FK
end StatMech
