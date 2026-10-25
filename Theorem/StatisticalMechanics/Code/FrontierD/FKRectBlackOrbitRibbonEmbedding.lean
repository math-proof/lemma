/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectRibbonCellResidueEmbed_injective
    (M : ℕ) (_hM : 0 < M) :
    Function.Injective (fkRectRibbonCellResidueEmbed M) := by
  rintro ⟨i, r⟩ ⟨j, s⟩ h
  have hval := congrArg (fun z : ZMod (8 * M) => z.val) h
  simp only [fkRectRibbonCellResidueEmbed, ZMod.val_natCast] at hval
  have hi : 8 * i.val + r.val < 8 * M := by omega
  have hj : 8 * j.val + s.val < 8 * M := by omega
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hval
  have hij : i.val = j.val := by omega
  have hrs : r.val = s.val := by omega
  exact Prod.ext (Fin.ext hij) (Fin.ext hrs)

end
end StatMech.FrontierD
