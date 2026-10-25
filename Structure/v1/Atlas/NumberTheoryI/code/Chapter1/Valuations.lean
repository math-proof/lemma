/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/Valuations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


noncomputable section

structure DiscreteValuation (k : Type*) [Field k] where
  val : Valuation k (WithZero (Multiplicative ℤ))
  surj : Function.Surjective val

end
