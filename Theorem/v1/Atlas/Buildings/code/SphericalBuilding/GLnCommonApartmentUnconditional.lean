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
set_option maxHeartbeats 1600000


namespace GLnBuilding

open Submodule Module

variable {k : Type*} [Field k]


section ChamberToCompleteFlag

/-- In a strictly increasing list, indexed elements at strictly increasing positions are
strictly increasing. -/
theorem isChain_getElem_lt {α : Type*} [Preorder α] {l : List α} (hc : l.IsChain (· < ·))
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    l[i] < l[j] := by
  induction hij with
  | refl =>
    exact (List.isChain_iff_getElem.mp hc) i (by omega)
  | step _ ih =>
    have hstep := (List.isChain_iff_getElem.mp hc) _ (by omega)
    exact lt_trans (ih (by omega)) hstep

end ChamberToCompleteFlag
end GLnBuilding
