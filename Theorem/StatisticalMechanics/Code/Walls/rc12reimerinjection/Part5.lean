/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11core.Part3
import Def.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part5
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxHeartbeats 4000000 in


theorem rc12_reflInjSearch_fin2_holds :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ →
      rc12_reflInjSearch 𝒜 ℬ = true := by
  decide


set_option maxHeartbeats 2000000 in


theorem rc12_naiveUnion_refuted :
    rc12_naiveUnionSearch ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 2))) Finset.univ = false := by
  decide

end StatMech.Walls
