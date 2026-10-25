/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6deficitform.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc6relabelinvariance.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc6eventdowncompression
import Theorem.StatisticalMechanics.Code.Walls.rc6blmonovariant
import Theorem.StatisticalMechanics.Code.Walls.rc6hallavailable.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc6canonicalwitness.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc6overlapsplit
import Theorem.StatisticalMechanics.Code.Walls.rc6localmirror.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc5_core.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


section CanonMirror

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in


noncomputable def rc6_canonMirror (A B : Set (ConfigSpace α)) (ω : ConfigSpace α) :
    ConfigSpace α :=
  rc6_mirrorL (↑(canonicalWitness A B ω).2.2) ω

end CanonMirror
end StatMech.Walls
