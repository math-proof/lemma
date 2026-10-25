/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldTransverseAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualTranslated
open MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicGraph.shiftGraphHom
    (P : PeriodicGraph V) (z : Site 2) : P.graph →g P.graph where
  toFun := P.shift z
  map_rel' := fun {_ _} h => (P.shift_adj z _ _).2 h

end StatMech.FK.PeriodicPlanar
