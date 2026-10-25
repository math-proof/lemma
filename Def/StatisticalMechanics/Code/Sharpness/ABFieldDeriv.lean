/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Russo
import Theorem.StatisticalMechanics.Code.Sharpness.AizenmanBarskyUncond
import Theorem.StatisticalMechanics.Code.Sharpness.BetaReparam
open MeasureTheory Set Finset Function
open scoped NNReal ENNReal

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

open ConfigSpace StatMech


variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def edgeWeightV (p : E → ℝ) (ω : ConfigSpace E) (e : E) : ℝ :=
  if ω e then p e else 1 - p e


noncomputable def configWeightV (p : E → ℝ) (ω : ConfigSpace E) : ℝ :=
  ∏ e, edgeWeightV p ω e


noncomputable def weightOffV (p : E → ℝ) (e : E) (ω : ConfigSpace E) : ℝ :=
  ∏ j ∈ univ.erase e, edgeWeightV p ω j


noncomputable def probV (p : E → ℝ) (A : Set (ConfigSpace E)) : ℝ :=
  ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * configWeightV p ω


noncomputable def pivotalProbV (p : E → ℝ) (A : Set (ConfigSpace E)) (e : E) : ℝ :=
  ∑ ω, (Set.indicator {ω | IsPivotal e A ω} (fun _ => (1 : ℝ)) ω) * configWeightV p ω


end Sharpness
end StatMech
