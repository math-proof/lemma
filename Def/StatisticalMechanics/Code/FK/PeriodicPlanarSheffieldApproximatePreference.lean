/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceClosure
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldApproximatePreference
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice


def rectangleEndpointPreferenceError {n m : Nat}
    (bottom top left right : PreferenceGridVertex n m → Real) : Real :=
  (∑ i : Fin (n + 1), max (top (i, 0) - bottom (i, 0)) 0) +
  (∑ i : Fin (n + 1),
    max (bottom (i, Fin.last m) - top (i, Fin.last m)) 0) +
  (∑ j : Fin (m + 1), max (right (0, j) - left (0, j)) 0) +
  ∑ j : Fin (m + 1),
    max (left (Fin.last n, j) - right (Fin.last n, j)) 0

end StatMech.FK.PeriodicPlanar
