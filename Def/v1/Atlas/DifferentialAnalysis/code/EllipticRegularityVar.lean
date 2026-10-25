/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/EllipticRegularityVar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
open scoped SchwartzMap
open TemperedDistribution MvPolynomial


noncomputable section

namespace DifferentialOperators

variable {n : ℕ}


/-- An elliptic parametrix for the constant-coefficient differential operator with symbol `P`:
a tempered distribution `E` such that `P(D) E - δ₀` is smooth and `E` has singular support at
the origin only. Existence is provided by `parametrix_exists_with_singSupp`. -/
def ellipticParametrix (m : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (parametrix_exists_with_singSupp hP).choose

end DifferentialOperators
end
