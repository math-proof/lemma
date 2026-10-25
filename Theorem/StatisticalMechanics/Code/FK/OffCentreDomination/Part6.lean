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
import Def.StatisticalMechanics.Code.FK.OffCentreDomination.Part9
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


variable {Gin Gout ιV}

variable (Gin Gout ιV)

variable (bdryOut : Vout → Prop) [DecidablePred bdryOut]


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

theorem ocd_outsideOnly_self_not_inner (ψ : ConfigSpace (Sym2 Vout)) {u : Vout}
    (hu : ocd_OutsideOnly Gout ιV bdryOut ψ u) : ¬ ocd_IsInnerVert ιV u :=
  hu u (SimpleGraph.Reachable.refl u)

theorem ocd_outsideOnly_of_reachable (ψ : ConfigSpace (Sym2 Vout)) {u v : Vout}
    (hu : ocd_OutsideOnly Gout ιV bdryOut ψ u)
    (h : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable u v) :
    ocd_OutsideOnly Gout ιV bdryOut ψ v :=
  fun w hw => hu w (h.trans hw)

theorem ocd_outsideGraph_reachable_of_fullGraph_outsideOnly (hι : Function.Injective ιV)
    (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) {u w : Vout}
    (hu : ocd_OutsideOnly Gout ιV bdryOut ψ u)
    (h : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable u w) :
    (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable u w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail a b hua hadj ih =>
      have ha_out : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable u a := ih
      have ha_not_inner : ¬ ocd_IsInnerVert ιV a := hu a ha_out
      exact ha_out.trans (ocd_fullGraph_adj_of_outside hι ω ψ ha_not_inner hadj).reachable

end FK
end StatMech
