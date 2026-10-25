/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part2


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


noncomputable def hexCyclicNewMid (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) : ℂ :=
  hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) +
    halfStep (hexInfra_headAccum h0 ts + t)


noncomputable def hexCyclicNewVertex (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) : ℂ :=
  hexCyclicNewMid a h0 ts t + halfStep (hexInfra_headAccum h0 ts + t)


end
end StatMech.Universality
