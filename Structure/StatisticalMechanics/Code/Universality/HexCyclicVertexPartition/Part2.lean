/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part3


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


structure HexCyclicLaunch (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (j : Fin 3) (ts : List ℤ) : Prop where
  endsAt : (ofTurns a h0 ts).EndsAt (labelMid v du j)
  lastVertex :
    labelMid v du j + halfStep (hexInfra_headAccum h0 ts) = v


end
end StatMech.Universality
