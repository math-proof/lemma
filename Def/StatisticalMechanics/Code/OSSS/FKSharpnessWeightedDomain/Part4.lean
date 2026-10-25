/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part3
open scoped BigOperators Classical
open Finset Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


variable {Vin Vout : Type*} [Fintype Vin] [Fintype Vout]

variable [DecidableEq Vin] [DecidableEq Vout]

variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]

variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]

variable (iota : Vin -> Vout)

variable (bdryOut : Vout -> Prop) [DecidablePred bdryOut]


def ocd_ParamCompatible (pfIn : Sym2 Vin -> Real)
    (pfOut : Sym2 Vout -> Real) : Prop :=
  forall e, pfIn e = pfOut (ocd_innerEdge iota e)


noncomputable def ocd_psiEdgeFactorW (pfOut : Sym2 Vout -> Real)
    (psi : ConfigSpace (Sym2 Vout)) : Real :=
  ∏ e ∈ Gout.edgeFinset.filter
      (fun e => e ∉ Set.range (ocd_innerEdge iota)),
    if psi e then pfOut e else 1 - pfOut e

end FK
end StatMech
