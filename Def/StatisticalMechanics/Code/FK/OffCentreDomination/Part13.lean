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
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part8
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


variable {Gin Gout ιV bdryOut}

noncomputable def ocd_fullComponentEquiv (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).ConnectedComponent ⊕
        ocd_OutsideOnlyComp Gout ιV bdryOut ψ ≃
      (ocd_fullGraph Gout ιV bdryOut ω ψ).ConnectedComponent :=
  Equiv.ofBijective (ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ)
    ⟨ocd_fullComponentMap_injective hι hadjm ω ψ, ocd_fullComponentMap_surjective hι hadjm ω ψ⟩


noncomputable def ocd_outsideShift (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (bdryOut : Vout → Prop) [DecidablePred bdryOut]
    (ψ : ConfigSpace (Sym2 Vout)) : ℕ :=
  Nat.card (ocd_OutsideOnlyComp Gout ιV bdryOut ψ)


end FK
end StatMech
