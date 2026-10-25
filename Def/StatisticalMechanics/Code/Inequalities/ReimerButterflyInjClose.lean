/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubleCoverClose.Part4
open Finset
open scoped FinsetFamily


namespace StatMech

open ConfigSpace


def rbi_cfg (a b : Bool) : ConfigSpace (Fin 2) := ![a, b]

end StatMech
