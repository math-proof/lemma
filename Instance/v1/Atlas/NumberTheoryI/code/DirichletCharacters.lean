/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Abbrev.v1.Atlas.NumberTheoryI.code.DirichletCharacters


namespace CharacterGroup

variable {G : Type*} [CommGroup G] [Fintype G]

instance instCommGroup : CommGroup (CharacterGroup G) :=
  inferInstance

instance hasEnoughRootsOfUnity_complex_exponent :
    HasEnoughRootsOfUnity ℂ (Monoid.exponent G) := by
  haveI : NeZero (Monoid.exponent G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  infer_instance

instance instFinite : Finite (CharacterGroup G) :=
  Finite.of_equiv G
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some.symm.toEquiv

end CharacterGroup
