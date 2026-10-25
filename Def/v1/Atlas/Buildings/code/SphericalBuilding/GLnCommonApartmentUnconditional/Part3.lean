/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderFrame.Part2
import Lemma.Fin.JhLine.in.SpacesAddVal1.of.IsStrictFlag.IsStrictFlag
import Lemma.Submodule.Any_LtAndLtAndEqFinrankK_AddFinrankK1.of.LeAddFinrankK2_FinrankK.Lt
import Def.v1.Atlas.Buildings.code.SphericalBuilding.AdaptedBasisProof
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.GLnCommonApartmentUnconditional.Part3
set_option maxHeartbeats 1600000


namespace GLnBuilding

open Submodule Module

variable {k : Type*} [Field k]


variable (k) (n : ℕ)

/-- Main: any two chambers $σ, τ$ admit a common frame, namely the Jordan–Hölder frame of
their associated complete flags. -/
noncomputable def twoChamberFrameHypUnconditional (hn : n ≥ 2) :
    TwoChamberFrameHyp k n where
  frame_of_two_chambers := fun σ τ hσ_chamber hτ_chamber => by

    let σ' := chamberToCompleteFlag σ hσ_chamber hn
    let τ' := chamberToCompleteFlag τ hτ_chamber hn
    have hσ_strict := chamberToCompleteFlag_isStrictFlag σ hσ_chamber hn
    have hτ_strict := chamberToCompleteFlag_isStrictFlag τ hτ_chamber hn

    let F := jordanHolderFrame σ' τ' hσ_strict hτ_strict
    refine ⟨F, ?_, ?_⟩
    ·
      intro V hV
      obtain ⟨i, hi⟩ := chamberToCompleteFlag_contains σ hσ_chamber hn V hV
      rw [← hi]
      exact jordanHolderFrame_compatible_sigma σ' τ' hσ_strict hτ_strict i
    ·
      intro V hV
      obtain ⟨j, hj⟩ := chamberToCompleteFlag_contains τ hτ_chamber hn V hV
      rw [← hj]
      exact jordanHolderFrame_compatible_tau σ' τ' hσ_strict hτ_strict j


/-- The common-apartment property holds unconditionally for $\mathrm{GL}_n(k)$: any two
flags lie in the apartment of some frame. The case $n \le 1$ is vacuous. -/
noncomputable def commonApartmentHypUnconditional :
    CommonApartmentHyp k n where
  refine_flags := fun σ τ => by
    by_cases hn : n ≤ 1
    · exact (subspaceFlag_empty_of_le_one' hn σ).elim
    · push_neg at hn
      have hn2 : n ≥ 2 := by omega
      exact (commonApartmentFromHyps n hn2
        (twoChamberFrameHypUnconditional k n hn2)).refine_flags σ τ

end GLnBuilding
