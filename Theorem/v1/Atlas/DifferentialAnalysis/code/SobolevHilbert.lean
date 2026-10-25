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
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert


noncomputable section

open MeasureTheory

namespace SobolevHilbert

/-- Elements of `SobolevSpace n m` are `j`-times continuously differentiable for any `j ≤ m`. -/
theorem sobolevSpace_contDiff {n m : ℕ}
    (u : SobolevEmbedding.SobolevSpace n m) (j : ℕ) (hj : j ≤ m) :
    ContDiff ℝ (j : ℕ∞) u.toFun :=
  u.contDiff_toFun.of_le (Nat.cast_le.mpr hj)


/-- The `j`-th iterated Fréchet derivative of the sum of two `SobolevSpace n m` elements is in `L^2`. -/
theorem sobolevSpace_add_memLp {n m : ℕ}
    (u v : SobolevEmbedding.SobolevSpace n m) (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have huf : ContDiff ℝ (j : ℕ∞) u.toFun := sobolevSpace_contDiff u j hj
  have hvf : ContDiff ℝ (j : ℕ∞) v.toFun := sobolevSpace_contDiff v j hj
  have heq : (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) =
      (fun x => iteratedFDeriv ℝ j u.toFun x + iteratedFDeriv ℝ j v.toFun x) := by
    ext x
    rw [iteratedFDeriv_add_apply huf.contDiffAt hvf.contDiffAt]
  rw [heq]
  exact (u.iteratedFDeriv_memLp j hj).add (v.iteratedFDeriv_memLp j hj)


/-- The triangle inequality for the `ℓ^2` norm of finite sequences indexed by `Finset.range k`. -/
lemma l2_triangle_range (k : ℕ) (a b : ℕ → ℝ) :
    Real.sqrt (∑ j ∈ Finset.range k, (a j + b j) ^ 2) ≤
    Real.sqrt (∑ j ∈ Finset.range k, (a j) ^ 2) +
    Real.sqrt (∑ j ∈ Finset.range k, (b j) ^ 2) := by
  simp_rw [Finset.sum_range]
  have h := @norm_add_le (PiLp 2 (fun _ : Fin k => ℝ)) _
    (WithLp.toLp 2 (fun i : Fin k => a i)) (WithLp.toLp 2 (fun i : Fin k => b i))
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  exact h


/-- Monotonicity of `sqrt (∑ c j ^ 2)` in pointwise nonnegative bounds `c j ≤ d j`. -/
lemma sqrt_sum_sq_mono {k : ℕ} {c d : ℕ → ℝ}
    (hc : ∀ j ∈ Finset.range k, 0 ≤ c j)
    (hle : ∀ j ∈ Finset.range k, c j ≤ d j) :
    Real.sqrt (∑ j ∈ Finset.range k, (c j) ^ 2) ≤
    Real.sqrt (∑ j ∈ Finset.range k, (d j) ^ 2) := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j hj
  exact pow_le_pow_left₀ (hc j hj) (hle j hj) 2


/-- Triangle inequality for the Sobolev `H^m` norm on `SobolevSpace n m`. -/
theorem sobolevSpace_norm_triangle {n m : ℕ}
    (u v : SobolevEmbedding.SobolevSpace n m) :
    Real.sqrt (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2 volume).toReal ^ 2) ≤
    Real.sqrt (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2) +
    Real.sqrt (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume).toReal ^ 2) := by

  set au := fun j => (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal
  set av := fun j => (eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume).toReal
  set auv := fun j =>
    (eLpNorm (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2 volume).toReal

  have hle : ∀ j ∈ Finset.range (m + 1), auv j ≤ au j + av j := by
    intro j hj
    have hjm : j ≤ m := by rw [Finset.mem_range] at hj; omega

    have huf : ContDiff ℝ (j : ℕ∞) u.toFun := sobolevSpace_contDiff u j hjm
    have hvf : ContDiff ℝ (j : ℕ∞) v.toFun := sobolevSpace_contDiff v j hjm

    have heq : (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) =
        (fun x => iteratedFDeriv ℝ j u.toFun x + iteratedFDeriv ℝ j v.toFun x) := by
      ext x; rw [iteratedFDeriv_add_apply huf.contDiffAt hvf.contDiffAt]

    have hu_lp := u.iteratedFDeriv_memLp j hjm
    have hv_lp := v.iteratedFDeriv_memLp j hjm

    have hmin : eLpNorm (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2 volume ≤
        eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume +
        eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume := by
      rw [heq]
      exact eLpNorm_add_le hu_lp.aestronglyMeasurable hv_lp.aestronglyMeasurable one_le_two

    have hfin : eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume +
        eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hu_lp.eLpNorm_ne_top, hv_lp.eLpNorm_ne_top⟩
    calc auv j
        = (eLpNorm (fun x => iteratedFDeriv ℝ j (u.toFun + v.toFun) x) 2 volume).toReal := rfl
      _ ≤ (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume +
            eLpNorm (fun x => iteratedFDeriv ℝ j v.toFun x) 2 volume).toReal :=
          ENNReal.toReal_mono hfin hmin
      _ = au j + av j :=
          ENNReal.toReal_add hu_lp.eLpNorm_ne_top hv_lp.eLpNorm_ne_top

  have hnn : ∀ j ∈ Finset.range (m + 1), 0 ≤ auv j := fun _ _ => ENNReal.toReal_nonneg

  calc Real.sqrt (∑ j ∈ Finset.range (m + 1), auv j ^ 2)
      ≤ Real.sqrt (∑ j ∈ Finset.range (m + 1), (au j + av j) ^ 2) :=
        sqrt_sum_sq_mono hnn hle
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (m + 1), au j ^ 2) +
        Real.sqrt (∑ j ∈ Finset.range (m + 1), av j ^ 2) :=
        l2_triangle_range (m + 1) au av


/-- A continuous Sobolev function that vanishes almost everywhere vanishes identically. -/
theorem sobolevSpace_ae_eq_zero_imp_eq_zero {n m : ℕ}
    (u : SobolevEmbedding.SobolevSpace n m)
    (hae : u.toFun =ᵐ[volume] 0) : u.toFun = 0 := by
  have hcont : Continuous u.toFun :=
    (sobolevSpace_contDiff u 0 (Nat.zero_le m)).continuous
  exact (hcont.ae_eq_iff_eq volume continuous_zero).mp hae

/-- Separation property: if every Sobolev semi-norm of `u` vanishes, then the underlying function is zero. -/
theorem sobolevSpace_norm_separation {n m : ℕ}
    (u : SobolevEmbedding.SobolevSpace n m)
    (h : ∀ j, j ≤ m →
      (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal = 0) :
    u.toFun = 0 := by

  have h0 := h 0 (Nat.zero_le m)
  have hm0 := u.iteratedFDeriv_memLp 0 (Nat.zero_le m)

  rw [ENNReal.toReal_eq_zero_iff] at h0
  have hsnorm : eLpNorm (fun x => iteratedFDeriv ℝ 0 u.toFun x) 2 volume = 0 :=
    h0.elim id (fun htop => absurd hm0.eLpNorm_lt_top (not_lt.mpr (le_of_eq htop.symm)))

  have hae : (fun x => iteratedFDeriv ℝ 0 u.toFun x) =ᵐ[volume] 0 :=
    (eLpNorm_eq_zero_iff hm0.1 two_ne_zero).mp hsnorm

  have hae_f : u.toFun =ᵐ[volume] 0 := by
    apply hae.mono
    intro x hx
    simp only [Pi.zero_apply] at hx ⊢
    have : ‖iteratedFDeriv ℝ 0 u.toFun x‖ = 0 := by rw [hx]; simp
    rw [norm_iteratedFDeriv_zero] at this
    exact norm_eq_zero.mp this

  exact sobolevSpace_ae_eq_zero_imp_eq_zero u hae_f


/-- Extensionality for `SobolevSpace n m`: equality is determined by the underlying function. -/
@[ext]
theorem SobolevEmbedding.SobolevSpace.ext' {n m : ℕ}
    {u v : SobolevEmbedding.SobolevSpace n m} (h : u.toFun = v.toFun) : u = v := by
  cases u; cases v; simp_all


end SobolevHilbert
end
