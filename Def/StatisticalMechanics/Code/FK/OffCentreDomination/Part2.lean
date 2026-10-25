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
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination
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


def ocd_AdjMatch : Prop := ∀ x y, Gin.Adj x y ↔ Gout.Adj (ιV x) (ιV y)


noncomputable def ocd_psiExt (ψ : ConfigSpace (Sym2 Vout)) (ω : ConfigSpace (Sym2 Vin)) :
    ConfigSpace (Sym2 Vout) :=
  fun e => if h : e ∈ Set.range (ocd_innerEdge ιV) then ω h.choose else ψ e


noncomputable def ocd_innerRestrict (ρ : ConfigSpace (Sym2 Vout)) : ConfigSpace (Sym2 Vin) :=
  fun e => ρ (ocd_innerEdge ιV e)


noncomputable def ocd_innerEdgeFinset : Finset (Sym2 Vout) :=
  Finset.univ.image (ocd_innerEdge ιV)

end FK
end StatMech
