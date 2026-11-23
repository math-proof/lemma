/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ParametrixBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Structure.v1.Atlas.DifferentialAnalysis.code.PseudoDiffOps
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.PseudoDiffOps
open DifferentialOperators
open TemperedDistribution MvPolynomial
open scoped SchwartzMap Pointwise

public section

/-- A constant-coefficient differential operator preserves compact support: if the tempered
distribution `F` vanishes outside a compact `K`, then so does `P(D) F`. -/


namespace DifferentialOperators

variable {n : ℕ}


end DifferentialOperators
noncomputable section

end
