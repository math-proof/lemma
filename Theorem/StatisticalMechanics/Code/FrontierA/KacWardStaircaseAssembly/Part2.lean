/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly.Part2


namespace StatMech.FrontierA

open scoped NNReal

open Set


theorem KWStairParameterData.parameter_strictMono
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (i : Fin n) :
    StrictMono (data.parameter i) :=
  Fin.strictMono_iff_lt_succ.mpr (data.parameter_strict i)

end StatMech.FrontierA
