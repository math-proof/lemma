/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CommutatorEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.EllipticLowerBound
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.EllipticLowerBound
import Structure.v1.Atlas.DifferentialAnalysis.code.CommutatorEstimates
open scoped SchwartzMap
open TemperedDistribution MvPolynomial


noncomputable section

namespace DifferentialOperators

variable {n : ℕ}

/-- The parametrix symbol associated to a polynomial `P` of order `m` and a
smooth cutoff `φ`: `q(ξ) = (1 − φ(ξ)) / P_m(ξ)` where `P_m` is the principal
symbol, with the convention `q(ξ) = 0` wherever the principal symbol
vanishes. -/
def parametrixSymbol (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (φ : SmoothCutoff n) : (Fin n → ℝ) → ℂ :=
  fun ξ =>
    if evalPrincipalSymbolReal m P ξ = 0 then 0
    else (1 - (φ.toFun ξ : ℂ)) / evalPrincipalSymbolReal m P ξ

end DifferentialOperators
end
