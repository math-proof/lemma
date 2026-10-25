/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1816.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.DirichletCharacters
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.DirichletCharacters
import Theorem.v1.Atlas.NumberTheoryI.code.Cor1816
open DirichletCharacter


namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]


noncomputable def toPrimCharDvd {m : ℕ} (χ : DirichletCharacter R m) : PrimCharDvd R m where
  d := χ.conductor
  hdvd := χ.conductor_dvd_level
  χ := χ.primitiveCharacter
  hprim := χ.primitiveCharacter_isPrimitive


noncomputable def fromPrimCharDvd {m : ℕ} (p : PrimCharDvd R m) : DirichletCharacter R m :=
  changeLevel p.hdvd p.χ


end DirichletCharacter
