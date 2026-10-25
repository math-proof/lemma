/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/EllipticLowerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Normed.Module.RCLike.Real
open scoped SchwartzMap
open TemperedDistribution MvPolynomial Metric


noncomputable section

namespace DifferentialOperators

variable {n : ℕ}

/-- The principal symbol of `P` (a polynomial in the cotangent variables of order `m`)
evaluated at a real covector `ξ ∈ ℝⁿ`, viewed as a complex number by inclusion `ℝ ↪ ℂ`. -/
def evalPrincipalSymbolReal (m : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    (Fin n → ℝ) → ℂ :=
  fun ξ => MvPolynomial.eval (fun i => (ξ i : ℂ)) (principalSymbol n m P)

end DifferentialOperators
end
