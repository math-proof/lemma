/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalSheffieldFKG.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]


def PeriodicPlaneEmbedding.finiteRectTargetConnection
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V) :
    Set (ConfigSpace (Sym2 (E.RectVertex a b c d))) :=
  {eta | ∃ x' y : E.RectVertex a b c d, x'.1 = x ∧ y.1 ∈ T ∧
    (FK.openSub (E.rectGraph a b c d) eta).Reachable x' y}


def PeriodicPlaneEmbedding.rectTargetConnectionEvent
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  E.rectRestrict a b c d ⁻¹'
    E.finiteRectTargetConnection a b c d x T

end StatMech.FK.PeriodicPlanar
