/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCode.Part2


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

@[simp] theorem fkRectZModFin_val {M : ℕ} (hM : 0 < M) (p : ZMod M) :
    (fkRectZModFin hM p).val = p.val := by
  rfl

theorem fkRectZModFin_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (fkRectZModFin hM) := by
  letI : NeZero M := ⟨hM.ne'⟩
  intro p q h
  exact ZMod.val_injective M (congrArg Fin.val h)

theorem fkRectZModFin_add_one {M : ℕ} (hM : 0 < M) (p : ZMod M) :
    fkRectZModFin hM (p + 1) =
      finitePeriodicSucc hM (fkRectZModFin hM p) := by
  letI : NeZero M := ⟨hM.ne'⟩
  apply Fin.ext
  simp only [fkRectZModFin, ZMod.val_add, Fin.val_mk, finitePeriodicSucc]
  rw [ZMod.val_one_eq_one_mod, Nat.add_mod_mod]

theorem fkRectZModFin_sub_one {M : ℕ} (hM : 0 < M) (p : ZMod M) :
    fkRectZModFin hM (p - 1) =
      SixVertexArrows.cyclicPred hM (fkRectZModFin hM p) := by
  letI : NeZero M := ⟨hM.ne'⟩
  have hleft := fkRectZModFin_add_one hM (p - 1)
  rw [sub_add_cancel] at hleft
  rw [hleft, svCyclicPred_finitePeriodicSucc]


end
end StatMech.FrontierD
