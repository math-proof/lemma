/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeightedSobolevSchwartz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbeddingTheorem
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbeddingTheorem
open scoped ZeroAtInfty SchwartzMap


noncomputable section

namespace SobolevEmbedding

/-- Multiplying a `Cᵏ` function vanishing at infinity by the inverse of a
power of the Japanese bracket `⟨x⟩^{-p}` again gives a `Cᵏ` function
vanishing at infinity, with the prescribed pointwise formula. -/
theorem japaneseBracket_pow_ne_zero_complex {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (pow_pos (TestFunctions.japaneseBracket_pos n x) k).ne'

end SobolevEmbedding
end
