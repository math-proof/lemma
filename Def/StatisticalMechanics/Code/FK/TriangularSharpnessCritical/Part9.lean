/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part8
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


noncomputable def triangularTransBoxToBufferedAt (k : Nat) (x : Site 2) (m : Nat)
    (hm : triangularTransBufferLevel k x ≤ m) :
    TriangularTransBoxVertex (2 * k) x → triangular.BufferedVertex m :=
  fun y => triangular.bufferedVertexInclLE hm
    (triangularTransBoxToBuffered k x y)

end StatMech.FK.PeriodicPlanar
