/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part11


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


noncomputable def triangularTorusSweepEdgeOdds
    (L : ℕ) [Fact (2 < L)] (y0 y1 y2 : ℝ)
    (e : (triangularTorusGraph L).edgeSet) : ℝ :=
  triHexDirectionOdds y0 y1 y2
    ((triHexTorusTriangleSweepEdgeEquiv L).symm e).2


noncomputable def hexagonalTorusSweepEdgeOdds
    (L : ℕ) [Fact (2 < L)] (y0 y1 y2 : ℝ)
    (e : (hexagonalTorusGraph L).edgeSet) : ℝ :=
  triHexDirectionOdds y0 y1 y2
    ((triHexTorusStarSweepEdgeEquiv L).symm e).2

end StatMech.FK.PeriodicPlanar
