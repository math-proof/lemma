/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexSeparation


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


open Classical in


noncomputable def specialMidCount (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts : List ℤ) : ℕ :=
  (if PassesThrough a h0 ts (v + du) then 1 else 0)
    + (if PassesThrough a h0 ts (v + hexOmega * du) then 1 else 0)
    + (if PassesThrough a h0 ts (v + hexOmega ^ 2 * du) then 1 else 0)


end StatMech.Universality
