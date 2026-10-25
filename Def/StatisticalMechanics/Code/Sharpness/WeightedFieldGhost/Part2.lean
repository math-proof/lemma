/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.HcovAssembly.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.WeightedFieldGhost
open Finset BigOperators SimpleGraph
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

namespace WeightedFieldGhost

open StatMech.Ising

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


open StatMech.Sharpness.FluxEdgeCopy (sourcePairDisconnSum endsM)

open StatMech.Sharpness.RandomCurrent (connK)

open StatMech.Sharpness.HcovAssembly


noncomputable def weightedBondDelta (β h : ℝ) (J : Sym2 V -> ℝ)
    (o : V) (e : Sym2 V) : ℝ :=
  sourcePairDisconnSum (withGhost G) β (ghostCoupling h β J)
    (hcaBondSource o e) ∅ (some o) none


noncomputable def weightedFieldDelta (β h : ℝ) (J : Sym2 V -> ℝ)
    (o z : V) : ℝ :=
  sourcePairDisconnSum (withGhost G) β (ghostCoupling h β J)
    (hcaFieldSource o z) ∅ (some o) none

end WeightedFieldGhost
end Sharpness
end StatMech
