module
public import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
open NumberField IsDedekindDomain
open scoped NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FinitePlaceAbsValue.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {K : Type*} [Field K] [NumberField K]


namespace FinitePlace

noncomputable def toAbsoluteValue (v : HeightOneSpectrum (𝓞 K)) : AbsoluteValue K ℝ :=
  HeightOneSpectrum.adicAbv K v

end FinitePlace
