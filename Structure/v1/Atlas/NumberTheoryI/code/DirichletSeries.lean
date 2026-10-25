/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.NumberTheoryI.code.ProductFormula
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ProductFormula


noncomputable section

open scoped Classical

structure ArakelovDivisor (K : Type*) [Field K] (hG : IsGlobalField K) where
  val : hG.PlaceType → ℝ
  pos : ∀ v, 0 < val v
  finite_support : Set.Finite {v | val v ≠ 1}

end
