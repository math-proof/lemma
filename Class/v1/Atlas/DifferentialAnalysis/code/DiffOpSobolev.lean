/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevDerivatives
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevDerivatives
import Mathlib.Algebra.MvPolynomial.Degrees
import Def.v1.Atlas.DifferentialAnalysis.code.DiffOpSobolev
open scoped SchwartzMap ContDiff FourierTransform
open DifferentialOperators SobolevEmbedding SobolevSpace MvPolynomial Filter Topology MeasureTheory


noncomputable section

namespace DiffOpSobolev

variable (n : ℕ)

/-- Action of a constant-coefficient differential operator `P(D)` on a distribution
represented by a Sobolev `H^s` function: the result is represented by an `H^{s-k}`
function, when the polynomial has degree at most `k ≤ s`. -/
class `H^s` into `H^{s-k}` (Melrose, Section 10, Prop 10.2). -/

end DiffOpSobolev
end
