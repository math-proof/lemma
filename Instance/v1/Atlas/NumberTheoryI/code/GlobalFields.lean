/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Def.v1.Atlas.NumberTheoryI.code.GlobalFields


noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

namespace AbsoluteValue

variable {K : Type*} [Field K]

instance nontrivialAbsValSetoid :
    Setoid { v : AbsoluteValue K ℝ // ¬v.IsTrivial } where
  r v w := v.val.IsEquiv w.val
  iseqv := {
    refl := fun _ => AbsoluteValue.IsEquiv.refl _
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

end AbsoluteValue
end
