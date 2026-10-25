/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HilbertSpace
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Class.v1.Atlas.DifferentialAnalysis.code.HilbertSpace
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part2


noncomputable section

open MeasureTheory

namespace SobolevHilbert

/-- The Sobolev norm is invariant under negation. -/
lemma sobolevNorm_neg' {n m : ℕ} (u : SobolevEmbedding.SobolevSpace n m) :
    sobolevNorm (-u) = sobolevNorm u := by
  simp only [sobolevNorm, sobolevSpace_neg_toFun, iteratedFDeriv_neg]
  congr 1; apply Finset.sum_congr rfl; intro j _
  have : (fun x => (-iteratedFDeriv ℝ j u.toFun) x) = -(fun x => iteratedFDeriv ℝ j u.toFun x) := rfl
  rw [this, eLpNorm_neg]

/-- The Sobolev norm of the zero element is zero. -/
lemma sobolevNorm_zero' (n m : ℕ) : sobolevNorm (0 : SobolevEmbedding.SobolevSpace n m) = 0 := by
  simp only [sobolevNorm, sobolevSpace_zero_toFun]
  suffices h : ∀ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j (0 : EuclideanSpace ℝ (Fin n) → ℂ) x) 2 volume).toReal ^ 2 = 0 by
    simp_all
  intro j _
  have : (fun x => iteratedFDeriv ℝ j (0 : EuclideanSpace ℝ (Fin n) → ℂ) x) = 0 := by ext x; simp
  simp [this]

/-- If the Sobolev norm of `u` is zero, then `u = 0`. -/
lemma sobolevNorm_eq_zero_iff {n m : ℕ} (u : SobolevEmbedding.SobolevSpace n m)
    (h : sobolevNorm u = 0) :
    u = 0 := by
  have hsq : ∀ j ∈ Finset.range (m + 1),
      (0 : ℝ) ≤ (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2 :=
    fun _ _ => sq_nonneg _
  have hsum := Real.sqrt_eq_zero (Finset.sum_nonneg hsq) |>.mp h
  have := Finset.sum_eq_zero_iff_of_nonneg hsq |>.mp hsum
  have hcomp : ∀ j, j ≤ m →
      (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal = 0 := by
    intro j hj
    have := this j (Finset.mem_range.mpr (by omega))
    exact sq_eq_zero_iff.mp this
  exact SobolevEmbedding.SobolevSpace.ext' (sobolevSpace_norm_separation u hcomp)

end SobolevHilbert
end
