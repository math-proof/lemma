/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarAspectOrientationNoGo
open MeasureTheory Set


namespace StatMech.FK.PeriodicPlanar

def aspectOrientationCounterexampleConfig : ConfigSpace (Sym2 (Fin 2)) :=
  fun _ => false


def aspectOrientationCertainEvent : Set (ConfigSpace (Sym2 (Fin 2))) :=
  Set.univ


def aspectOrientationAbsentEvent : Set (ConfigSpace (Sym2 (Fin 2))) :=
  {omega | omega s(0, 1) = true}

end StatMech.FK.PeriodicPlanar
