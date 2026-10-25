/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.FK.LimitCommutation.Part5
import Theorem.StatisticalMechanics.Code.FK.MonotoneVolumeLimit
import Def.StatisticalMechanics.Code.FK.OffCentreDomination
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin] [Fintype Vout] [DecidableEq Vout]

variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]

variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]

variable (ιV : Vin → Vout)


theorem ocd_innerEdge_injective (hι : Function.Injective ιV) :
    Function.Injective (ocd_innerEdge ιV) :=
  Sym2.map.injective hι

theorem ocd_innerEdge_mk (x y : Vin) :
    ocd_innerEdge ιV s(x, y) = s(ιV x, ιV y) := by
  rw [ocd_innerEdge, Sym2.map_mk]

theorem ocd_isInnerVert_iff_range (v : Vout) :
    ocd_IsInnerVert ιV v ↔ ∃ x, ιV x = v := Iff.rfl


end FK
end StatMech
