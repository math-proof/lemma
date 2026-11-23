/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeakConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Algebra.MvPolynomial.Eval
public import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators

@[expose] public section

open scoped SchwartzMap
open TemperedDistribution MvPolynomial Filter Topology


noncomputable section

namespace DifferentialOperators

variable {n : ℕ}

section Prop_11_2

variable {ι : Type*}

end Prop_11_2
end DifferentialOperators
end
