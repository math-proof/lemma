/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

def crossRatio {K : Type*} [Field K] (z₁ z₂ z₃ z₄ : K) : K :=
  (z₁ - z₃) * (z₂ - z₄) / ((z₁ - z₄) * (z₂ - z₃))


end StatMech.SLE
