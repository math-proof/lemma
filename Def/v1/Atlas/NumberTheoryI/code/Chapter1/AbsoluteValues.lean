/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.Ostrowski
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.FieldTheory.Finite.Basic
import Abbrev.v1.Atlas.NumberTheoryI.code.Chapter1.AbsoluteValues


noncomputable section

def AbsoluteValue.IsArchimedean {k : Type*} [Field k] (v : AbsoluteValue k ℝ) : Prop :=
  ¬ IsNonarchimedean v

def AbsoluteValue.IsEquivalent {k : Type*} [Field k]
    (v w : AbsoluteValue k ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ x : k, w x = (v x) ^ α

end
