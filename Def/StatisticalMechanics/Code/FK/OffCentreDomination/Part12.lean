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
import Instance.StatisticalMechanics.Code.FK.OffCentreDomination.Part7
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

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


noncomputable def ocd_fullComponentMap (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).ConnectedComponent ⊕
        ocd_OutsideOnlyComp Gout ιV bdryOut ψ →
      (ocd_fullGraph Gout ιV bdryOut ω ψ).ConnectedComponent
  | Sum.inl c => c.lift (fun x => (ocd_fullGraph Gout ιV bdryOut ω ψ).connectedComponentMk (ιV x))
      (fun a b p _ => ConnectedComponent.sound
        (ocd_fullGraph_reachable_of_innerGraph hι hadjm ω ψ p.reachable))
  | Sum.inr c => c.1.lift (fun v => (ocd_fullGraph Gout ιV bdryOut ω ψ).connectedComponentMk v)
      (fun a b p _ => ConnectedComponent.sound
        (p.reachable.mono (ocd_outsideGraph_le_fullGraph ω ψ)))

end FK
end StatMech
