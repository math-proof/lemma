/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1835.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.NumberTheoryI.code.DirichletCharacters
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.DirichletCharacters
@[expose] public section

namespace CharacterGroup

variable {G : Type*} [CommGroup G] [Fintype G]

noncomputable instance instFintype : Fintype (CharacterGroup G) := Fintype.ofFinite _

end CharacterGroup
