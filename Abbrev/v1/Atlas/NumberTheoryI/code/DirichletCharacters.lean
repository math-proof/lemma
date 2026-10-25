/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Mathlib.NumberTheory.DirichletCharacter.Basic


abbrev CharacterGroup (G : Type*) [CommGroup G] [Fintype G] := G →* ℂˣ

