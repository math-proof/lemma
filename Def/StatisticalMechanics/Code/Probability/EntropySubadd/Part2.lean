/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part11
import Theorem.StatisticalMechanics.Code.Probability.EntropySubadd
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def esd_ent (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  OSSS.expect ν (fun ω => esd_Phi (g ω)) - esd_Phi (OSSS.expect ν g)


noncomputable def esd_entCoord (p : ℝ) (g : ConfigSpace E → ℝ) (e : E) (ω : ConfigSpace E) : ℝ :=
  p * esd_Phi (g (StatMech.setOpen e ω)) + (1 - p) * esd_Phi (g (StatMech.setClosed e ω))
    - esd_Phi (OSSS.condMean (OSSS.bernoulliWeight p) e g ω)


def esd_PosWeight (ν : E → Bool → ℝ) : Prop := ∀ e b, 0 < ν e b

end StatMech.Probability
