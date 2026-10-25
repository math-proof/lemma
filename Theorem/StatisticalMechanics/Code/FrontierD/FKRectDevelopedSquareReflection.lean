/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectRowReflection_val (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) :
    (fkRectRowReflection R center y).val =
      (2 * center + R.height - y.val) % R.height :=
  rfl

theorem fkRectRowReflection_involutive (R : FKRectTorus) (center : Nat) :
    Function.Involutive (fkRectRowReflection R center) := by
  intro y
  apply Fin.ext
  let A := 2 * center + R.height
  let r := (A - y.val) % R.height
  have hyA : y.val <= A := by
    dsimp [A]
    omega
  have hrH : r < R.height := Nat.mod_lt _ R.height_pos
  have hrA : r <= A := by
    dsimp [A]
    omega
  have hmod : r ≡ A - y.val [MOD R.height] :=
    Nat.mod_modEq (A - y.val) R.height
  have hsub : A - r ≡ A - (A - y.val) [MOD R.height] :=
    Nat.ModEq.sub hrA (Nat.sub_le A y.val) (Nat.ModEq.refl A) hmod
  have hAy : A - (A - y.val) = y.val := Nat.sub_sub_self hyA
  change (A - r) % R.height = y.val
  rw [Nat.mod_eq_of_modEq (hAy ▸ hsub) y.isLt]

@[simp] theorem fkRectRowReflection_twice (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) :
    fkRectRowReflection R center (fkRectRowReflection R center y) = y :=
  fkRectRowReflection_involutive R center y


end
end StatMech.FrontierD
