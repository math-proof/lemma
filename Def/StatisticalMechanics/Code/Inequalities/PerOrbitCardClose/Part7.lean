/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part6
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def poc_rbi_p1 : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  (rbi_cfg false false, rbi_cfg false true)

def poc_rbi_p2 : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  (rbi_cfg false true, rbi_cfg false false)


end StatMech
