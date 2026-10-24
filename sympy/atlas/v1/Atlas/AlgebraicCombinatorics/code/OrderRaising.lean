/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrderRaising.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SetFamily.Shadow

open Finset SpernerProperty
open scoped FinsetFamily

namespace SpernerProperty

section UpwardLYM

variable {α : Type*}

noncomputable def upNbhd (n i : ℕ) (s : {s : Finset (Fin n) // s.card = i}) :
    Finset {t : Finset (Fin n) // t.card = i + 1} :=
  Finset.univ.filter fun t => s.val ⊂ t.val
