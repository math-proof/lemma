/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1835.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.DirichletCharacters
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.DirichletCharacters


namespace CharacterGroup

variable {G : Type*} [CommGroup G] [Fintype G]

noncomputable instance instFintype : Fintype (CharacterGroup G) := Fintype.ofFinite _

end CharacterGroup
