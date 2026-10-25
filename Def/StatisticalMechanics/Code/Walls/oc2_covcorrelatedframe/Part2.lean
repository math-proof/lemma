/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc2_covcorrelatedframe
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.MonotonicMeasure

open StatMech.OSSS.MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def oc2_covCorrSum (p q : ℝ) (f : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, oc2_covCorr G p q f (oc2_coordRead e)


noncomputable def oc2_thetaCorr (p q : ℝ) (f : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  oc2_meanCorr G p q f


end Walls
end StatMech
