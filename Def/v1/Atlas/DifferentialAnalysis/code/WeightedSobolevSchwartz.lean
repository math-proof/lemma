/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeightedSobolevSchwartz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbeddingTheorem
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbeddingTheorem
import Theorem.v1.Atlas.DifferentialAnalysis.code.WeightedSobolevSchwartz
open scoped ZeroAtInfty SchwartzMap


noncomputable section

namespace SobolevEmbedding

/-- Step in Melrose Prop. 10.4: a function lying in every weighted Sobolev
space gives rise, for each smoothness index `j` and weight `l`, to a `Cⱼ`
function vanishing at infinity whose value at `x` is `⟨x⟩^l · f(x)`.
Combines the Sobolev embedding theorem with multiplication by an inverse
weight. -/
def schwartz_mul_japaneseBracket_pow {n k : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    { g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) //
      ∀ x, g x = (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) * f x } := by

  set φ : EuclideanSpace ℝ (Fin n) → ℂ :=
    fun x => (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) with hφ_def

  have hφ : Function.HasTemperateGrowth φ := by
    simp only [hφ_def, TestFunctions.japaneseBracket]

    have h1 : (fun x : EuclideanSpace ℝ (Fin n) =>
        (↑((Real.sqrt (1 + ‖x‖ ^ 2)) ^ k) : ℂ)) =
      Complex.ofReal ∘ (fun x => (Real.sqrt (1 + ‖x‖ ^ 2)) ^ k) := by
      ext x; simp
    rw [h1]
    apply Function.Complex.hasTemperateGrowth_ofReal.comp

    have h2 : (fun x : EuclideanSpace ℝ (Fin n) =>
        (Real.sqrt (1 + ‖x‖ ^ 2)) ^ k) =
      (fun x => (1 + ‖x‖ ^ 2) ^ (k / 2 : ℝ)) := by
      ext x
      have hpos : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by positivity
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hpos]
      ring_nf
    rw [h2]
    exact Function.hasTemperateGrowth_one_add_norm_sq_rpow _ _

  exact ⟨SchwartzMap.smulLeftCLM ℂ φ f, fun x => by
    rw [SchwartzMap.smulLeftCLM_apply_apply hφ]
    exact smul_eq_mul (φ x) (f x)⟩

end SobolevEmbedding
end
