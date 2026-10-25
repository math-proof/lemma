/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeUnitPacking.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeWeightedCounterexample
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


theorem weightedCollisionEnds_loopless :
    ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      ¬ (weightedCollisionEnds i).IsDiag := by
  intro i _
  fin_cases i <;> simp [weightedCollisionEnds, Sym2.mk_isDiag_iff]


end StatMech.GrahamGHS.FourColor
