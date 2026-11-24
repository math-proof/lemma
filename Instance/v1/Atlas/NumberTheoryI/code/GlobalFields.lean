module
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Artinian.Module
public import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Def.v1.Atlas.NumberTheoryI.code.GlobalFields


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
