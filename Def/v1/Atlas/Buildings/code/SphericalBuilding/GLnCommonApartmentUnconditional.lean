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
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.GLnCommonApartmentUnconditional
set_option maxHeartbeats 1600000


namespace GLnBuilding

open Submodule Module

variable {k : Type*} [Field k]


section ChamberToCompleteFlag

/-- Convert a chamber (maximal `SubspaceFlag`) into the corresponding `CompleteFlag` indexed
by $\mathrm{Fin}(n+1)$, where $\mathrm{spaces}\ 0 = \bot$ and $\mathrm{spaces}\ n = \top$. -/
noncomputable def chamberToCompleteFlag {n : ℕ} (σ : SubspaceFlag k n)
    (hchamber : IsChamber k n σ) (hn : n ≥ 2) : CompleteFlag k n where
  spaces i :=
    if h : i.val = 0 then ⊥
    else if h2 : i.val = n then ⊤
    else σ.chain[i.val - 1]'(by rw [hchamber]; omega)
  monotone := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Fin.le_iff_val_le_val] at hab
    simp only
    split_ifs with ha0 haN hb0 hbN hb0' hbN' <;>
      first
        | exact bot_le
        | exact le_refl _
        | exact le_top
        | (exfalso; omega)
        | skip

    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · have ha1 : a - 1 < b - 1 := by omega
      exact le_of_lt (isChain_getElem_lt σ.chain_strictly_increasing
        (by rw [hchamber]; omega) (by rw [hchamber]; omega) ha1)
  bot_eq := by simp
  top_eq := by
    simp only
    split_ifs with h0
    · omega
    · rfl

end ChamberToCompleteFlag
end GLnBuilding
