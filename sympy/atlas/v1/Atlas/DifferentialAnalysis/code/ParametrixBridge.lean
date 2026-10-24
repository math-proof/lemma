/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ParametrixBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.PseudoDiffOps
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.PseudoDiffOps

open DifferentialOperators
open TemperedDistribution MvPolynomial
open scoped SchwartzMap Pointwise

noncomputable section

namespace DifferentialOperators

variable {n : ℕ}


/-- A constant-coefficient differential operator preserves compact support: if the tempered
distribution `F` vanishes outside a compact `K`, then so does `P(D) F`. -/
end DifferentialOperators
