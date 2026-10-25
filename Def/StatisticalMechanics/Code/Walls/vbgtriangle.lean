/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
open scoped BigOperators
open Finset


namespace StatMech

namespace Walls

namespace VBG

set_option linter.unusedSectionVars false

set_option linter.style.longLine false

set_option maxHeartbeats 800000


variable {Ω : Type*} [Fintype Ω]


noncomputable def vbg_exp (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, μ ω * f ω


noncomputable def vbg_cov (μ : Ω → ℝ) (f g : Ω → ℝ) : ℝ :=
  vbg_exp μ (fun ω => f ω * g ω) - vbg_exp μ f * vbg_exp μ g


noncomputable def vbg_var (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ := vbg_cov μ f f


noncomputable def vbg_condPlus (μ : Ω → ℝ) (Y : Ω → ℝ) (ω : Ω) : ℝ :=
  μ ω * Y ω / vbg_exp μ Y


noncomputable def vbg_condMinus (μ : Ω → ℝ) (Y : Ω → ℝ) (ω : Ω) : ℝ :=
  μ ω * (1 - Y ω) / (1 - vbg_exp μ Y)


noncomputable def vbg_covPlus (μ : Ω → ℝ) (Y f g : Ω → ℝ) : ℝ :=
  vbg_cov (vbg_condPlus μ Y) f g


noncomputable def vbg_varPlus (μ : Ω → ℝ) (Y f : Ω → ℝ) : ℝ :=
  vbg_var (vbg_condPlus μ Y) f


noncomputable def vbg_covMinus (μ : Ω → ℝ) (Y f g : Ω → ℝ) : ℝ :=
  vbg_cov (vbg_condMinus μ Y) f g


noncomputable def vbg_varMinus (μ : Ω → ℝ) (Y f : Ω → ℝ) : ℝ :=
  vbg_var (vbg_condMinus μ Y) f


end VBG
end Walls
end StatMech
