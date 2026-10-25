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
open scoped SchwartzMap ContDiff FourierTransform
open DifferentialOperators SobolevEmbedding SobolevSpace MvPolynomial Filter Topology MeasureTheory


noncomputable section

namespace DiffOpSobolev

variable (n : ℕ)

/-- A tempered distribution `u` lies in the Sobolev space `H^m` if it is represented
by integration against an element of `SobolevSpace n m`. -/
def IsInSobolev (m : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ f : SobolevSpace n m,
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      u φ = ∫ x : EuclideanSpace ℝ (Fin n), φ x • f x


end DiffOpSobolev
end
