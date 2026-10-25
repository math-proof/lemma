/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HeckeKL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.LieGroups.code.CompositionSeries
import Lemma.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
import Abbrev.v1.Atlas.LieGroups.code.HeckeKL.Part2


noncomputable section

open Polynomial

structure CoxeterGroupData where
  W : Type*
  grpInst : Group W
  finInst : Fintype W
  decEq : DecidableEq W
  simpleReflections : Finset W
  length : W → ℕ
  length_one : length 1 = 0
  length_simple : ∀ s ∈ simpleReflections, length s = 1
  simple_sq : ∀ s ∈ simpleReflections, s * s = 1
  bruhatLE : W → W → Prop
  bruhatLE_dec : ∀ y w, Decidable (bruhatLE y w)
  bruhat_refl : ∀ w, bruhatLE w w
  bruhat_trans : ∀ x y z, bruhatLE x y → bruhatLE y z → bruhatLE x z
  bruhat_antisymm : ∀ x y, bruhatLE x y → bruhatLE y x → x = y
  bruhat_length_le : ∀ y w, bruhatLE y w → length y ≤ length w
  bruhat_length_strict : ∀ y w, bruhatLE y w → y ≠ w → length y < length w
  exchange_left : ∀ s ∈ simpleReflections, ∀ w,
    length (s * w) = length w + 1 ∨ length (s * w) + 1 = length w
  descentRefl : W → W
  descentRefl_simple : ∀ y, y ≠ 1 → descentRefl y ∈ simpleReflections
  descentRefl_length : ∀ y, y ≠ 1 → length (descentRefl y * y) < length y
  descentRefl_of_mul : ∀ s ∈ simpleReflections, ∀ w,
    length (s * w) = length w + 1 → descentRefl (s * w) = s

end
