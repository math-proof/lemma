/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CompactSobolevEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WeightedSobolevSchwartz
import Def.v1.Atlas.DifferentialAnalysis.code.WeightedSobolevSchwartz
import Instance.v1.Atlas.DifferentialAnalysis.code.CompactSobolevEmbedding.Part2
open MeasureTheory Filter Topology
open scoped ZeroAtInfty


noncomputable section

namespace SchwartzWeightedSobolev

/-- The iterated Fréchet derivatives (up to order `k`) of the `Cᵏ` witness of
a Schwartz test function lie in `L²` with respect to Lebesgue measure. -/
def allWeightedSobolevToSchwartz {n : ℕ}
    (w : MemAllWeightedSobolev n) :
    { u : TestFunctions.SchwartzTestFunctionSpace n // u.toFun = w.toFun } := by


  have hf : ∀ k : ℕ, ∃ u : SobolevEmbedding.SobolevSpace n k,
      u.toFun = fun x =>
        (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) * w.toFun x := by
    intro k
    refine ⟨(w.mem_weighted k).witness, ?_⟩
    funext x
    have hcons := w.consistent k x


    have hne : (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) ≠ 0 :=
      SobolevEmbedding.japaneseBracket_pow_ne_zero_complex x k
    simp only [WeightedSobolevSpace.toFun] at hcons
    field_simp at hcons ⊢
    exact hcons.symm

  refine ⟨⟨w.toFun, fun j l => ?_⟩, rfl⟩

  let ⟨v, hv⟩ := SobolevEmbedding.weightedSobolev_to_contDiffZeroAtInfty w.toFun hf j l
  refine ⟨⟨v⟩, fun x => ?_⟩

  change w.toFun x = (↑(TestFunctions.japaneseBracket n x ^ l) : ℂ)⁻¹ *
    v.toZeroAtInftyContinuousMap x
  have hv_x : v.toZeroAtInftyContinuousMap x =
    (↑(TestFunctions.japaneseBracket n x ^ l) : ℂ) * w.toFun x := congr_fun hv x
  rw [hv_x]
  rw [inv_mul_cancel_left₀ (SobolevEmbedding.japaneseBracket_pow_ne_zero_complex x l)]

/-- Plain version of `allWeightedSobolevToSchwartz` discarding the proof of
the pointwise identity. -/
def allWeightedSobolevToSchwartz' {n : ℕ}
    (w : MemAllWeightedSobolev n) :
    TestFunctions.SchwartzTestFunctionSpace n :=
  (allWeightedSobolevToSchwartz w).val

/-- A function `f : ℝⁿ → ℂ` is Schwartz if it arises as the underlying
function of some element of `SchwartzTestFunctionSpace n`. -/
@[simp]

def IsSchwartz (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∃ u : TestFunctions.SchwartzTestFunctionSpace n, u.toFun = f

/-- A function `f : ℝⁿ → ℂ` lies in every weighted Sobolev space if it arises
as the underlying function of some `MemAllWeightedSobolev n`. -/
def IsInAllWeightedSobolev (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∃ w : MemAllWeightedSobolev n, w.toFun = f

end SchwartzWeightedSobolev
end
