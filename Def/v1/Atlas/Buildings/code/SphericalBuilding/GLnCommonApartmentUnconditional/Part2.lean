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
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.GLnCommonApartmentUnconditional.Part2
set_option maxHeartbeats 1600000


namespace GLnBuilding

open Submodule Module

variable {k : Type*} [Field k]


section TauCompatibility

/-- The set of indices $i$ whose Jordan–Hölder line lies inside $τ.\mathrm{spaces}\ j$,
defined via $\mathrm{jumpCol}(i+1) < j$. -/
noncomputable def tauWitness (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (j : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n =>
    (jumpCol σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)).val < j.val)

end TauCompatibility
end GLnBuilding
