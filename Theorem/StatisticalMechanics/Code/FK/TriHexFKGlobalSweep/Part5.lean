/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
import Def.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
open Finset
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Universality


theorem triHexFK_globalSweep_twoPointRatio_eq
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (hq : q ≠ 0) (hyprod : y0 * y1 * y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (terminal : ι → Fin 3 → V)
    (external : (ι → ThreeTerminalConnectivity) → Real)
    (x y : V) :
    starFKGlobalSweepRatio q y0Star y1Star y2Star external
        (triHexFKTerminalTwoPointObservable terminal x y) =
      triangleFKGlobalSweepRatio y0 y1 y2 external
        (triHexFKTerminalTwoPointObservable terminal x y) :=
  triHexFK_globalSweepRatio_eq hq hyprod h0 h1 h2 hsurface
    external (triHexFKTerminalTwoPointObservable terminal x y)

end StatMech.FK.PeriodicPlanar
