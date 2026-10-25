/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1816.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.DirichletCharacters
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.DirichletCharacters
import Theorem.v1.Atlas.NumberTheoryI.code.Cor1816.Part2
open DirichletCharacter


namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]


noncomputable def cor_18_16_M_equivMul_Ghat (m : ℕ) :
    DirichletCharacter R m ≃* ((ZMod m)ˣ →* Rˣ) :=
  MulChar.mulEquivToUnitHom


noncomputable def cor_18_16_M_equiv_X (m : ℕ) (hm : m ≠ 0) :
    DirichletCharacter R m ≃ PrimCharDvd R m where
  toFun := toPrimCharDvd
  invFun := fromPrimCharDvd
  left_inv := fromPrimCharDvd_toPrimCharDvd
  right_inv := toPrimCharDvd_fromPrimCharDvd hm

end DirichletCharacter
