/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.TriHexPeriodicPlaneEmbedding.Part2
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicStraightIntersection.Part2
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

noncomputable def triangularPeriodicPlaneEmbedding :
    PeriodicPlaneEmbedding triangular :=
  triangularPeriodicPlaneEmbedding_of_intersection
    triangularStraightEdgeIntersection


noncomputable def hexagonalPeriodicPlaneEmbedding :
    PeriodicPlaneEmbedding hexagonal :=
  hexagonalPeriodicPlaneEmbedding_of_intersection
    hexagonalStraightEdgeIntersection

end StatMech.FK.PeriodicPlanar
