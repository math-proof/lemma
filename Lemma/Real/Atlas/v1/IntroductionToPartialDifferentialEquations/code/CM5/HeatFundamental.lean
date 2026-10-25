import Mathlib
import sympy.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM5.HeatFundamental
open Set MeasureTheory Filter Topology Real HeatFundamental


namespace HeatFundamental

/--
[norm_sq_le_euclidNormSq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma norm_sq_le_euclidNormSq
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  ‖x‖ ^ 2 ≤ euclidNormSq x := by
-- proof
  unfold euclidNormSq
  by_cases hn : n = 0
  · subst hn; simp [Pi.norm_def]
  · have hfin_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn))
    rw [Pi.norm_def]
    obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup' hfin_ne (fun b => ‖x b‖₊)
    rw [← Finset.sup'_eq_sup hfin_ne, hi₀]
    have : (↑‖x i₀‖₊ : ℝ) = |x i₀| := by
      simp [NNNorm.nnnorm, Real.norm_eq_abs]
    rw [this, sq_abs]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i₀)

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_time_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_time_deriv
  {n : ℕ}
  {D : ℝ}
  {t : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : D > 0)
  (ht : t > 0) :
-- imply
  deriv (fun s => heatKernel D s x) t = heatKernel D t x * (euclidNormSq x / (4 * D * t ^ 2) - ↑n / (2 * t)) := by
-- proof
  have hc_pos : (4 : ℝ) * π * D > 0 := by positivity
  have hct_pos : (4 : ℝ) * π * D * t > 0 := by positivity
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hct_ne : (4 : ℝ) * π * D * t ≠ 0 := ne_of_gt hct_pos
  have hD_ne : D ≠ 0 := ne_of_gt hD
  set C := euclidNormSq x / (4 * D)
  set p := (n : ℝ) / 2
  suffices h_main : HasDerivAt (fun s => heatKernel D s x)
    (heatKernel D t x * (euclidNormSq x / (4 * D * t ^ 2) - ↑n / (2 * t))) t from
    h_main.deriv
  have h_eq : (fun s => heatKernel D s x) =ᶠ[nhds t]
    (fun s => (4 * π * D * s) ^ (-p) * exp (-C * s⁻¹)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    unfold heatKernel euclidNormSq
    have hcs_pos : (4 : ℝ) * π * D * s > 0 := by positivity
    congr 1
    · rw [rpow_neg (le_of_lt hcs_pos), div_eq_mul_inv, one_mul]
    · congr 1
      have hs_ne : s ≠ 0 := ne_of_gt hs
      simp only [C, euclidNormSq]
      field_simp
  rw [h_eq.hasDerivAt_iff]
  have hA : HasDerivAt (fun s => (4 * π * D * s) ^ (-p))
    ((4 * π * D) * (-p) * (4 * π * D * t) ^ (-p - 1)) t := by
    have h_inner : HasDerivAt (fun s => (4 : ℝ) * π * D * s) ((4 : ℝ) * π * D) t := by
      simpa using (hasDerivAt_id t).const_mul ((4 : ℝ) * π * D)
    exact h_inner.rpow_const (Or.inl hct_ne)
  have hB : HasDerivAt (fun s => exp (-C * s⁻¹))
    (exp (-C * t⁻¹) * (C * t⁻¹ ^ 2)) t := by
    have h_inv : HasDerivAt (fun s => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht_ne
    have h_inner : HasDerivAt (fun s => -C * s⁻¹) (-C * (-(t ^ 2)⁻¹)) t :=
      h_inv.const_mul (-C)
    have h_exp := h_inner.exp
    convert h_exp using 1
    ring
  have h_prod := hA.mul hB
  apply h_prod.congr_deriv
  have hrpow_rel : (4 * π * D * t) ^ (-p - 1) =
    (4 * π * D * t) ^ (-p) * (4 * π * D * t)⁻¹ := by
    rw [show -p - 1 = -p + (-1) from by ring, rpow_add hct_pos, rpow_neg_one]
  have h_hk_val : heatKernel D t x = (4 * π * D * t) ^ (-p) * exp (-C * t⁻¹) :=
    h_eq.self_of_nhds
  rw [h_hk_val, hrpow_rel]
  simp only [C, p, euclidNormSq]
  field_simp
  ring

end HeatFundamental

namespace HeatFundamental

/--
[euclidNormSq_update](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma euclidNormSq_update
  {n : ℕ}
  {x : Fin n → ℝ}
  {i : Fin n}
  {s : ℝ} :
-- imply
  euclidNormSq (Function.update x i s) = euclidNormSq x - (x i) ^ 2 + s ^ 2 := by
-- proof
  unfold euclidNormSq
  conv_lhs => arg 2; ext j; rw [Function.update_apply]
  trans (s ^ 2 + ∑ j ∈ Finset.univ.erase i, x j ^ 2)
  · rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro j hj; simp [(Finset.mem_erase.mp hj).1]
  · have : ∑ j : Fin n, x j ^ 2 = x i ^ 2 + ∑ j ∈ Finset.univ.erase i, x j ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    linarith

end HeatFundamental

namespace HeatFundamental

/--
[fderiv_eq_deriv_update](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma fderiv_eq_deriv_update
  {n : ℕ}
  {f : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
  {i : Fin n}
  {f' : ℝ}
-- given
  (hf : HasDerivAt (fun s => f (Function.update x i s)) f' (x i))
  (hdf : DifferentiableAt ℝ f x) :
-- imply
  fderiv ℝ f x (Pi.single i 1) = f' := by
-- proof
  have hupd : HasFDerivAt (Function.update x i)
    (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) (x i) :=
    hasFDerivAt_update x (x i)
  have hf_at : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    rw [Function.update_eq_self]; exact hdf.hasFDerivAt
  have h_chain := hf_at.comp (x i) hupd
  have h_deriv : HasDerivAt (fun s => f (Function.update x i s))
    ((fderiv ℝ f x).comp (ContinuousLinearMap.pi
      (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1) (x i) :=
    h_chain.hasDerivAt
  have h_eq := h_deriv.unique hf
  rw [← h_eq]
  simp [ContinuousLinearMap.comp_apply]
  congr 1; ext j
  simp [Pi.single_apply]
  split <;> simp

end HeatFundamental

namespace HeatFundamental

/--
[differentiableAt_euclidNormSq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma differentiableAt_euclidNormSq
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  DifferentiableAt ℝ (@euclidNormSq n) x := by
-- proof
  unfold euclidNormSq; fun_prop

end HeatFundamental

namespace HeatFundamental

/--
[differentiableAt_heatKernel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma differentiableAt_heatKernel
  {n : ℕ}
  {D t : ℝ}
  {x : Fin n → ℝ} :
-- imply
  DifferentiableAt ℝ (@heatKernel n D t) x := by
-- proof
  unfold heatKernel; fun_prop

end HeatFundamental

namespace HeatFundamental

/--
[hasDerivAt_gaussianExp_exponent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma hasDerivAt_gaussianExp_exponent
  {n : ℕ}
  {x : Fin n → ℝ}
  {i : Fin n}
  {D t : ℝ} :
-- imply
  HasDerivAt (fun s => -(euclidNormSq (Function.update x i s)) / (4 * D * t)) (-(2 * x i) / (4 * D * t)) (x i) := by
-- proof
  have h_eq : (fun s => -(euclidNormSq (Function.update x i s)) / (4 * D * t)) =
    (fun s => (-(euclidNormSq x) + (x i) ^ 2 - s ^ 2) / (4 * D * t)) := by
    ext s; rw [euclidNormSq_update]; ring
  rw [h_eq]
  exact (HasDerivAt.div_const ((hasDerivAt_const _ _).sub
    (by simpa using hasDerivAt_pow 2 (x i))) _).congr_deriv (by ring)

end HeatFundamental

namespace HeatFundamental

/--
[hasDerivAt_gaussianExp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma hasDerivAt_gaussianExp
  {n : ℕ}
  {x : Fin n → ℝ}
  {i : Fin n}
  {D t : ℝ}
-- given
  (hD : D > 0)
  (ht : t > 0) :
-- imply
  HasDerivAt (fun s => exp (-(euclidNormSq (Function.update x i s)) / (4 * D * t))) (exp (-(euclidNormSq x) / (4 * D * t)) * (-(x i) / (2 * D * t))) (x i) := by
-- proof
  have h_exp := (hasDerivAt_gaussianExp_exponent x i D t).exp
  simp only [Function.update_eq_self] at h_exp
  exact h_exp.congr_deriv (by field_simp; ring)

end HeatFundamental

namespace HeatFundamental

/--
[hasDerivAt_update_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma hasDerivAt_update_linear
  {n : ℕ}
  {x : Fin n → ℝ}
  {i : Fin n}
  {D t : ℝ} :
-- imply
  HasDerivAt (fun s => -(Function.update x i s i) / (2 * D * t)) (-1 / (2 * D * t)) (x i) := by
-- proof
  have h_eq : (fun s => -(Function.update x i s i) / (2 * D * t)) =
    (fun s => -s / (2 * D * t)) := by
    ext s; simp [Function.update_self]
  rw [h_eq]
  exact ((hasDerivAt_id (x i)).neg.div_const _).congr_deriv (by ring)

end HeatFundamental

namespace HeatFundamental

/--
[hasDerivAt_gaussianExp_second](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma hasDerivAt_gaussianExp_second
  {n : ℕ}
  {x : Fin n → ℝ}
  {i : Fin n}
  {D t : ℝ}
-- given
  (hD : D > 0)
  (ht : t > 0) :
-- imply
  HasDerivAt (fun s => exp (-(euclidNormSq (Function.update x i s)) / (4 * D * t)) * (-(Function.update x i s i) / (2 * D * t))) (exp (-(euclidNormSq x) / (4 * D * t)) * ((x i) ^ 2 / (2 * D * t) ^ 2 - 1 / (2 * D * t))) (x i) := by
-- proof
  have hf := hasDerivAt_gaussianExp x i D t hD ht
  have hg := hasDerivAt_update_linear x i D t
  have h_prod := hf.mul hg
  simp only [Function.update_eq_self] at h_prod
  exact h_prod.congr_deriv (by field_simp; ring)

end HeatFundamental

namespace HeatFundamental

/--
[hasDerivAt_heatKernel_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma hasDerivAt_heatKernel_coord
  {n : ℕ}
  {y : Fin n → ℝ}
  {i : Fin n}
  {D t : ℝ}
-- given
  (hD : D > 0)
  (ht : t > 0) :
-- imply
  HasDerivAt (fun s => heatKernel D t (Function.update y i s)) (heatKernel D t y * (-(y i) / (2 * D * t))) (y i) := by
-- proof
  unfold heatKernel
  have h_gauss := hasDerivAt_gaussianExp y i D t hD ht
  have h := h_gauss.const_mul (1 / (4 * π * D * t) ^ ((n : ℝ) / 2))
  convert h using 1; ring

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_fderiv_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_fderiv_single
  {n : ℕ}
  {D t : ℝ}
  {y : Fin n → ℝ}
  {i : Fin n}
-- given
  (hD : D > 0)
  (ht : t > 0) :
-- imply
  fderiv ℝ (heatKernel D t) y (Pi.single i 1) = heatKernel D t y * (-(y i) / (2 * D * t)) :=
-- proof
  fderiv_eq_deriv_update _ y i _ (hasDerivAt_heatKernel_coord y i D t hD ht)
    (differentiableAt_heatKernel D t y)

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_partial_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_partial_eq
  {n : ℕ}
  {D t : ℝ}
  {i : Fin n}
-- given
  (hD : D > 0)
  (ht : t > 0) :
-- imply
  (fun y => fderiv ℝ (heatKernel D t) y (Pi.single i 1)) = (fun y => heatKernel D t y * (-(y i) / (2 * D * t))) := by
-- proof
  ext y; exact heatKernel_fderiv_single D t hD ht y i

end HeatFundamental

namespace HeatFundamental

/--
[hasDerivAt_heatKernel_second_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma hasDerivAt_heatKernel_second_coord
  {n : ℕ}
  {y : Fin n → ℝ}
  {i : Fin n}
  {D t : ℝ}
-- given
  (hD : D > 0)
  (ht : t > 0) :
-- imply
  HasDerivAt (fun s => heatKernel D t (Function.update y i s) * (-(Function.update y i s i) / (2 * D * t))) (heatKernel D t y * ((y i) ^ 2 / (2 * D * t) ^ 2 - 1 / (2 * D * t))) (y i) := by
-- proof
  unfold heatKernel
  have h_gauss := hasDerivAt_gaussianExp_second y i D t hD ht
  set P := 1 / (4 * π * D * t) ^ ((n : ℝ) / 2)
  have h := h_gauss.const_mul P
  convert h using 1
  · ext s; ring
  · ring

end HeatFundamental

namespace HeatFundamental

/--
[differentiableAt_heatKernel_partial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma differentiableAt_heatKernel_partial
  {n : ℕ}
  {D t : ℝ}
  {x : Fin n → ℝ}
  {i : Fin n} :
-- imply
  DifferentiableAt ℝ (fun y : Fin n → ℝ => heatKernel D t y * (-(y i) / (2 * D * t))) x := by
-- proof
  apply DifferentiableAt.mul
  · exact differentiableAt_heatKernel D t x
  · fun_prop

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_second_fderiv_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_second_fderiv_single
  {n : ℕ}
  {D t : ℝ}
  {x : Fin n → ℝ}
  {i : Fin n}
-- given
  (hD : D > 0)
  (ht : t > 0) :
-- imply
  fderiv ℝ (fun y => fderiv ℝ (heatKernel D t) y (Pi.single i 1)) x (Pi.single i 1) = heatKernel D t x * ((x i) ^ 2 / (2 * D * t) ^ 2 - 1 / (2 * D * t)) := by
-- proof
  rw [show (fun y => fderiv ℝ (heatKernel D t) y (Pi.single i 1)) =
    (fun y => heatKernel D t y * (-(y i) / (2 * D * t))) from
    heatKernel_partial_eq D t hD ht i]
  exact fderiv_eq_deriv_update _ x i _
    (hasDerivAt_heatKernel_second_coord x i D t hD ht)
    (differentiableAt_heatKernel_partial D t x i)

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_laplacian
  {n : ℕ}
  {D : ℝ}
  {t : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : D > 0)
  (ht : t > 0) :
-- imply
  laplacian (heatKernel D t) x = heatKernel D t x * (euclidNormSq x / (4 * D ^ 2 * t ^ 2) - ↑n / (2 * D * t)) := by
-- proof
  unfold laplacian
  simp_rw [heatKernel_second_fderiv_single D t hD ht x]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib]
  congr 1
  ·
    rw [← Finset.sum_div]
    unfold euclidNormSq
    congr 1; ring
  ·
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp; ring

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_solves_heat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_solves_heat
  {n : ℕ}
  {D : ℝ}
  {t : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  heatOperator D (fun s (y : Fin n → ℝ) => heatKernel D s y) t x = 0 := by
-- proof
  unfold heatOperator
  rw [heatKernel_time_deriv hD ht x, heatKernel_laplacian hD ht x]
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  field_simp
  ring

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_pos
  {n : ℕ}
  {D : ℝ}
  {t : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  0 < heatKernel D t x := by
-- proof
  unfold heatKernel
  apply mul_pos
  · apply div_pos one_pos
    apply rpow_pos_of_pos
    have : (0 : ℝ) < 4 * π := by positivity
    positivity
  · exact exp_pos _

end HeatFundamental

namespace HeatFundamental

/--
[euclidNormSq_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma euclidNormSq_pos
  {n : ℕ}
  {x : Fin n → ℝ}
-- given
  (hx : x ≠ 0) :
-- imply
  0 < euclidNormSq x := by
-- proof
  unfold euclidNormSq
  apply Finset.sum_pos'
  · intro i _; exact sq_nonneg _
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_eq_rpow_exp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_eq_rpow_exp
  {n : ℕ}
  {D : ℝ}
  {x : Fin n → ℝ}
  {t : ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  heatKernel D t x = 1 / (4 * π * D) ^ ((n : ℝ) / 2) * (t⁻¹ ^ ((n : ℝ) / 2) * exp (-(euclidNormSq x / (4 * D)) * t⁻¹)) := by
-- proof
  unfold heatKernel
  have h4piD_pos : (0 : ℝ) < 4 * π * D := by positivity
  have h1 : (4 * π * D * t) ^ ((n : ℝ) / 2) =
    (4 * π * D) ^ ((n : ℝ) / 2) * t ^ ((n : ℝ) / 2) := by
    rw [show (4 : ℝ) * π * D * t = (4 * π * D) * t from by ring]
    exact Real.mul_rpow h4piD_pos.le ht.le
  have h2 : -(euclidNormSq x) / (4 * D * t) = -(euclidNormSq x / (4 * D)) * t⁻¹ := by
    field_simp
  rw [h1, h2, one_div, mul_inv, ← inv_rpow ht.le, ← one_div]
  ring

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_limit_zero_away](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_limit_zero_away
  {n : ℕ}
  {D : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : 0 < D)
  (hx : x ≠ 0) :
-- imply
  Tendsto (fun t => heatKernel D t x) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
-- proof
  set c := euclidNormSq x / (4 * D)
  have hc : 0 < c := div_pos (euclidNormSq_pos hx) (by positivity)
  set K := 1 / (4 * π * D) ^ ((n : ℝ) / 2)
  have h_inv : Tendsto (fun t : ℝ => t⁻¹) (nhdsWithin 0 (Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h_rpow_exp : Tendsto (fun u : ℝ => u ^ ((n : ℝ) / 2) * exp (-c * u))
    atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n : ℝ) / 2) c hc
  have h_comp : Tendsto (fun t : ℝ => t⁻¹ ^ ((n : ℝ) / 2) * exp (-c * t⁻¹))
    (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    h_rpow_exp.comp h_inv
  have h_const_mul : Tendsto (fun t : ℝ => K * (t⁻¹ ^ ((n : ℝ) / 2) * exp (-c * t⁻¹)))
    (nhdsWithin 0 (Ioi 0)) (nhds (K * 0)) :=
    h_comp.const_mul K
  rw [mul_zero] at h_const_mul
  apply Tendsto.congr' _ h_const_mul
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (heatKernel_eq_rpow_exp hD ht).symm

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_limit_infinity_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_limit_infinity_at_zero
  {n : ℕ}
  {D : ℝ}
-- given
  (hn : 0 < n)
  (hD : 0 < D) :
-- imply
  Tendsto (fun t => heatKernel D t (0 : Fin n → ℝ)) (nhdsWithin 0 (Ioi 0)) atTop := by
-- proof
  have hsimp : ∀ t, heatKernel D t (0 : Fin n → ℝ) = 1 / (4 * π * D * t) ^ ((n : ℝ) / 2) := by
    intro t
    unfold heatKernel euclidNormSq
    simp [Finset.sum_const_zero, exp_zero]
  simp_rw [hsimp]
  set p := (n : ℝ) / 2 with hp_def
  have hp_pos : 0 < p := div_pos (Nat.cast_pos.mpr hn) two_pos
  have hnp : -p < 0 := neg_neg_of_pos hp_pos
  have h4piD_pos : (0 : ℝ) < 4 * π * D := by positivity
  have hg : Tendsto (fun t => 4 * π * D * t) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Tendsto (fun t : ℝ => 4 * π * D * t) (nhds 0) (nhds (4 * π * D * 0)) :=
      tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos h4piD_pos ht
  have hcomp : Tendsto ((fun x => x ^ (-p)) ∘ (fun t => 4 * π * D * t)) (nhdsWithin 0 (Ioi 0)) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero hnp).comp hg
  rw [tendsto_congr' _]
  · exact hcomp
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_apply]
    have h4piDt_nonneg : 0 ≤ 4 * π * D * t := le_of_lt (mul_pos h4piD_pos ht)
    rw [rpow_neg h4piDt_nonneg, one_div]

end HeatFundamental

namespace HeatFundamental

/--
[one_d_gaussian_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma one_d_gaussian_integral
  {D t : ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  ∫ x : ℝ, (1 / (4 * π * D * t) ^ ((1 : ℝ) / 2) * exp (-(x ^ 2) / (4 * D * t))) = 1 := by
-- proof
  have h4Dt_pos : 0 < 4 * D * t := by positivity
  have heq_fun : (fun x : ℝ => (1 / (4 * π * D * t) ^ ((1:ℝ) / 2) * exp (-(x ^ 2) / (4 * D * t)))) =
    (fun x : ℝ => (1 / (4 * π * D * t) ^ ((1:ℝ) / 2)) * exp (-(1/(4 * D * t)) * x ^ 2)) := by
    ext x; congr 2; ring
  rw [heq_fun, integral_const_mul, integral_gaussian (1 / (4 * D * t))]
  have h1 : π / (1 / (4 * D * t)) = 4 * π * D * t := by field_simp
  rw [h1]
  have h4piDt_pos : 0 < 4 * π * D * t := by positivity
  rw [Real.sqrt_eq_rpow, div_mul_cancel₀]
  exact ne_of_gt (rpow_pos_of_pos h4piDt_pos _)

end HeatFundamental

namespace HeatFundamental

/--
[gaussian_integral_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma gaussian_integral_eq_one
  {n : ℕ}
  {D : ℝ}
  {t : ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  ∫ x : Fin n → ℝ, heatKernel D t x = 1 := by
-- proof
  set f : ℝ → ℝ := fun y =>
    1 / (4 * π * D * t) ^ ((1 : ℝ) / 2) * exp (-(y ^ 2) / (4 * D * t))
  have h_eq : (fun x : Fin n → ℝ => heatKernel D t x) =
    (fun x : Fin n → ℝ => ∏ i, f (x i)) := by
    ext x
    unfold heatKernel euclidNormSq f
    have h4piDt_pos : 0 < 4 * π * D * t := by positivity
    rw [Finset.prod_mul_distrib]
    congr 1
    ·
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, one_pow]
      congr 1
      rw [← rpow_natCast ((4 * π * D * t) ^ ((1:ℝ)/2)) n,
        ← rpow_mul (le_of_lt h4piDt_pos)]
      congr 1; ring
    ·
      rw [← exp_sum]
      congr 1
      rw [← Finset.sum_div]
      congr 1
      simp [Finset.sum_neg_distrib]
  rw [h_eq, integral_fintype_prod_volume_eq_pow f]
  rw [show ∫ (x : ℝ), f x = 1 from one_d_gaussian_integral D t hD ht]
  simp [one_pow]

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_integral_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_integral_one
  {n : ℕ}
  {D : ℝ}
  {t : ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  ∫ x : Fin n → ℝ, heatKernel D t x = 1 :=
-- proof
  gaussian_integral_eq_one hD ht

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_lemma_1_0_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_lemma_1_0_2
  {n : ℕ}
  {D : ℝ}
-- given
  (hD : 0 < D)
  (hn : 0 < n) :
-- imply
  (∀ (x : Fin n → ℝ), x ≠ 0 → Filter.Tendsto (fun t => heatKernel D t x) (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧ (Filter.Tendsto (fun t => heatKernel D t (0 : Fin n → ℝ)) (nhdsWithin 0 (Ioi 0)) Filter.atTop) ∧ (∀ (t : ℝ), 0 < t → ∫ x : Fin n → ℝ, heatKernel D t x = 1) :=
-- proof
  ⟨fun x hx => heatKernel_limit_zero_away hD hx,
    heatKernel_limit_infinity_at_zero hn hD,
    fun t ht => heatKernel_integral_one hD ht⟩

end HeatFundamental

namespace HeatFundamental

/--
[wider_gaussian_1d](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma wider_gaussian_1d
  {D t : ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  ∫ x : ℝ, (1 / (4 * π * D * t) ^ ((1 : ℝ) / 2) * exp (-(x ^ 2) / (8 * D * t))) = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
-- proof
  have h4piDt_pos : 0 < 4 * π * D * t := by positivity
  have heq_fun : (fun x : ℝ => (1 / (4 * π * D * t) ^ ((1:ℝ) / 2) *
    exp (-(x ^ 2) / (8 * D * t)))) =
    (fun x : ℝ => (1 / (4 * π * D * t) ^ ((1:ℝ) / 2)) *
      exp (-(1/(8 * D * t)) * x ^ 2)) := by
    ext x; congr 2; ring
  rw [heq_fun, integral_const_mul, integral_gaussian (1 / (8 * D * t))]
  rw [show π / (1 / (8 * D * t)) = 8 * π * D * t from by field_simp]
  rw [Real.sqrt_eq_rpow, div_mul_eq_mul_div, one_mul]
  rw [show (8 : ℝ) * π * D * t = 2 * (4 * π * D * t) from by ring]
  rw [mul_rpow (by linarith : (0:ℝ) ≤ 2) (le_of_lt h4piDt_pos)]
  rw [mul_div_assoc, div_self (ne_of_gt (rpow_pos_of_pos h4piDt_pos _))]
  ring

end HeatFundamental

namespace HeatFundamental

/--
[wider_gaussian_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma wider_gaussian_integral
  {n : ℕ}
  {D : ℝ}
  {t : ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  ∫ x : Fin n → ℝ, (1 / (4 * π * D * t) ^ ((n : ℝ) / 2) * exp (-(euclidNormSq x) / (8 * D * t))) = (2 : ℝ) ^ ((n : ℝ) / 2) := by
-- proof
  set f : ℝ → ℝ := fun y =>
    1 / (4 * π * D * t) ^ ((1 : ℝ) / 2) * exp (-(y ^ 2) / (8 * D * t))
  have h_eq : (fun x : Fin n → ℝ =>
    1 / (4 * π * D * t) ^ ((n : ℝ) / 2) *
      exp (-(euclidNormSq x) / (8 * D * t))) =
    (fun x : Fin n → ℝ => ∏ i, f (x i)) := by
    ext x; unfold euclidNormSq f
    have h4piDt_pos : 0 < 4 * π * D * t := by positivity
    rw [Finset.prod_mul_distrib]; congr 1
    · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, one_pow]
      congr 1
      rw [← rpow_natCast ((4 * π * D * t) ^ ((1:ℝ)/2)) n,
        ← rpow_mul (le_of_lt h4piDt_pos)]
      congr 1; ring
    · rw [← exp_sum]; congr 1; rw [← Finset.sum_div]; congr 1
      simp [Finset.sum_neg_distrib]
  rw [h_eq, integral_fintype_prod_volume_eq_pow f]
  rw [show ∫ (x : ℝ), f x = (2 : ℝ) ^ ((1 : ℝ) / 2) from
    wider_gaussian_1d D t hD ht]
  simp only [Fintype.card_fin]
  rw [← rpow_natCast ((2 : ℝ) ^ ((1:ℝ)/2)) n,
    ← rpow_mul (by linarith : (0:ℝ) ≤ 2)]
  congr 1; ring

end HeatFundamental

namespace HeatFundamental

/--
[heat_tail_exp_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heat_tail_exp_bound
  {n : ℕ}
  {D : ℝ}
  {δ : ℝ}
  {t : ℝ}
-- given
  (hD : 0 < D)
  (hδ : δ > 0)
  (ht : 0 < t) :
-- imply
  |∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x| ≤ rexp (-(δ ^ 2 / (8 * D * t))) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
-- proof
  have hS : MeasurableSet {x : Fin n → ℝ | δ < ‖x‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hΓ_nn : ∀ x ∈ {x : Fin n → ℝ | δ < ‖x‖}, 0 ≤ heatKernel D t x :=
    fun x _ => le_of_lt (heatKernel_pos hD ht x)
  rw [abs_of_nonneg (setIntegral_nonneg hS hΓ_nn)]
  have hΓ_int : Integrable (fun x : Fin n → ℝ => heatKernel D t x) :=
    .of_integral_ne_zero (by rw [gaussian_integral_eq_one hD ht]; exact one_ne_zero)
  set W := fun x : Fin n → ℝ =>
    1 / (4 * π * D * t) ^ ((n : ℝ) / 2) *
      exp (-(euclidNormSq x) / (8 * D * t)) with hW_def
  have hW_int : Integrable (W : (Fin n → ℝ) → ℝ) :=
    .of_integral_ne_zero (by
      rw [wider_gaussian_integral hD ht]; exact ne_of_gt (by positivity))
  set g := fun x : Fin n → ℝ =>
    rexp (-(δ ^ 2 / (8 * D * t))) * W x with hg_def
  have hg_int : Integrable g := hW_int.const_mul _
  calc ∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x
    ≤ ∫ x in {x : Fin n → ℝ | δ < ‖x‖}, g x := by
      apply setIntegral_mono_on hΓ_int.integrableOn hg_int.integrableOn hS
      intro x hx; simp only [Set.mem_setOf_eq] at hx
      simp only [g, W, heatKernel]
      have h4p : 0 < 4 * π * D * t := by positivity
      have hp : 0 < 1 / (4 * π * D * t) ^ ((n : ℝ) / 2) :=
        div_pos one_pos (rpow_pos_of_pos h4p _)
      rw [show rexp (-(δ ^ 2 / (8 * D * t))) *
        (1 / (4 * π * D * t) ^ ((n : ℝ) / 2) *
          exp (-(euclidNormSq x) / (8 * D * t))) =
        1 / (4 * π * D * t) ^ ((n : ℝ) / 2) *
        (rexp (-(δ ^ 2 / (8 * D * t))) *
          exp (-(euclidNormSq x) / (8 * D * t))) from by ring]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hp)
      rw [← exp_add]; apply exp_le_exp.mpr
      have hδ_sq : δ ^ 2 ≤ euclidNormSq x :=
        le_of_lt (lt_of_lt_of_le (sq_lt_sq' (by linarith) hx)
          (norm_sq_le_euclidNormSq x))
      set E := euclidNormSq x
      show -E / (4 * D * t) ≤ -(δ ^ 2 / (8 * D * t)) + -E / (8 * D * t)
      have h8 : (0 : ℝ) < 8 * D * t := by positivity
      have key : -E / (4 * D * t) = -E / (8 * D * t) + -E / (8 * D * t) := by
        field_simp; ring
      rw [key]; gcongr; rw [neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_right hδ_sq (le_of_lt h8))
    _ ≤ ∫ x, g x := by
      apply setIntegral_le_integral hg_int
      exact Eventually.of_forall fun x =>
        mul_nonneg (le_of_lt (exp_pos _))
          (mul_nonneg (le_of_lt (div_pos one_pos
            (rpow_pos_of_pos (by positivity) _))) (le_of_lt (exp_pos _)))
    _ = rexp (-(δ ^ 2 / (8 * D * t))) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
      simp only [g, W]
      rw [integral_const_mul]; congr 1
      exact wider_gaussian_integral hD ht

end HeatFundamental

namespace HeatFundamental

/--
[exp_neg_large](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma exp_neg_large
  {target : ℝ}
-- given
  (htarget : target > 0) :
-- imply
  ∃ x₀ : ℝ, x₀ > 0 ∧ ∀ x : ℝ, x > x₀ → rexp (-x) < target := by
-- proof
  use 1 / target
  refine ⟨by positivity, fun x hx => ?_⟩
  have h1 : x + 1 ≤ rexp x := Real.add_one_le_exp x
  have h2 : rexp x > 1 / target := by linarith
  rw [Real.exp_neg, inv_lt_comm₀ (exp_pos x) htarget]
  rw [one_div] at h2; linarith

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_concentration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_concentration
  {n : ℕ}
  {D : ℝ}
  {δ : ℝ}
-- given
  (hD : 0 < D)
  (hδ : δ > 0) :
-- imply
  Tendsto (fun t => ∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
-- proof
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set C := (2 : ℝ) ^ ((n : ℝ) / 2)
  have hC_pos : C > 0 := by positivity
  set target := ε / C
  have htarget_pos : target > 0 := div_pos hε hC_pos
  obtain ⟨x₀, hx₀_pos, hx₀⟩ := exp_neg_large target htarget_pos
  set c := δ ^ 2 / (8 * D) with hc_def
  have hc_pos : c > 0 := by positivity
  use c / x₀, div_pos hc_pos hx₀_pos
  intro t ht_mem ht_dist
  have ht_pos : (0 : ℝ) < t := ht_mem
  have ht_lt : t < c / x₀ := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos ht_pos] at ht_dist
  rw [Real.dist_eq, sub_zero]
  have bound := heat_tail_exp_bound (n := n) hD δ hδ t ht_pos
  have hct : c / t > x₀ := by
    rw [lt_div_iff₀ hx₀_pos] at ht_lt
    rw [gt_iff_lt, lt_div_iff₀ ht_pos]
    linarith [mul_comm t x₀]
  have hc_eq : c / t = δ ^ 2 / (8 * D * t) := by rw [hc_def]; field_simp
  rw [hc_eq] at hct
  have hexp := hx₀ _ hct
  calc |∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x|
    ≤ rexp (-(δ ^ 2 / (8 * D * t))) * C := bound
    _ < target * C := mul_lt_mul_of_pos_right hexp hC_pos
    _ = ε := div_mul_cancel₀ ε (ne_of_gt hC_pos)

end HeatFundamental

namespace HeatFundamental

/--
[integrable_gauss_nD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma integrable_gauss_nD
  {n : ℕ}
  {c : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  Integrable (fun x : Fin n → ℝ => exp (-c * euclidNormSq x)) := by
-- proof
  have h_eq : (fun x : Fin n → ℝ => exp (-c * euclidNormSq x)) =
    (fun x : Fin n → ℝ => ∏ i, (fun y : ℝ => exp (-c * y ^ 2)) (x i)) := by
    ext x; unfold euclidNormSq; rw [← exp_sum]; congr 1; simp only [neg_mul, Finset.mul_sum]
  rw [h_eq, show (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
    from volume_pi.symm]
  exact Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hc)

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_mul_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_mul_integrable
  {n : ℕ}
  {D : ℝ}
  {φ : (Fin n → ℝ) → ℝ}
  {a b : ℝ}
  {t : ℝ}
-- given
  (hD : 0 < D)
  (hφ : Continuous φ)
  (_ha : 0 ≤ a)
  (_hb : 0 ≤ b)
  (hbound : ∀ x, |φ x| ≤ a * exp (b * euclidNormSq x))
  (ht : 0 < t)
  (htb : b * t < 1 / (4 * D)) :
-- imply
  Integrable (fun x => heatKernel D t x * φ x) := by
-- proof
  have h4Dt_pos : 0 < 4 * D * t := by positivity
  have hc_pos : 0 < 1 / (4 * D * t) - b := by
    have htb' : b * t * (4 * D) < 1 := by
      have := mul_lt_mul_of_pos_right htb (by positivity : 0 < 4 * D)
      rwa [div_mul_cancel₀ _ (ne_of_gt (by positivity : 0 < 4 * D))] at this
    rw [show 1 / (4 * D * t) - b = (1 - b * (4 * D * t)) / (4 * D * t) from by field_simp]
    exact div_pos (by nlinarith) h4Dt_pos
  set C := a / (4 * π * D * t) ^ ((n : ℝ) / 2)
  apply Integrable.mono' ((integrable_gauss_nD hc_pos).const_mul C)
  · apply Continuous.aestronglyMeasurable
    unfold heatKernel
    apply Continuous.mul
    · apply Continuous.mul
      · exact continuous_const
      · exact Real.continuous_exp.comp ((Continuous.div_const
        (Continuous.neg (continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)))) _)
    · exact hφ
  · apply Eventually.of_forall; intro x
    rw [Real.norm_eq_abs, abs_mul]
    have hK_pos : 0 < heatKernel D t x := by
      unfold heatKernel
      apply mul_pos (div_pos one_pos (rpow_pos_of_pos (by positivity) _)) (exp_pos _)
    rw [abs_of_pos hK_pos]
    calc heatKernel D t x * |φ x|
      ≤ heatKernel D t x * (a * exp (b * euclidNormSq x)) :=
        mul_le_mul_of_nonneg_left (hbound x) (le_of_lt hK_pos)
      _ = C * exp (-(1 / (4 * D * t) - b) * euclidNormSq x) := by
        unfold heatKernel C
        rw [show -(1 / (4 * D * t) - b) * euclidNormSq x =
          -(euclidNormSq x) / (4 * D * t) + b * euclidNormSq x from by ring]
        rw [exp_add]; ring

end HeatFundamental

namespace HeatFundamental

/--
[prefactor_identity_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma prefactor_identity_weighted
  {n : ℕ}
  {D t : ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  (2:ℝ) ^ ((n:ℝ)/2) * (1 / (4 * π * (2 * D) * t) ^ ((n:ℝ)/2)) = 1 / (4 * π * D * t) ^ ((n:ℝ)/2) := by
-- proof
  rw [show (4:ℝ) * π * (2 * D) * t = 2 * (4 * π * D * t) from by ring,
    mul_rpow (by linarith : (0:ℝ) ≤ 2) (le_of_lt (by positivity : (0:ℝ) < 4 * π * D * t)),
    one_div, one_div, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (by positivity : (2:ℝ) ^ ((n:ℝ)/2) ≠ 0), one_mul]

end HeatFundamental

namespace HeatFundamental

/--
[exp_bound_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma exp_bound_weighted
  {s D b t : ℝ}
-- given
  (hs : 0 ≤ s)
  (hD : 0 < D)
  (ht : 0 < t)
  (htb : b * t ≤ 1 / (8 * D)) :
-- imply
  exp (-s / (4 * D * t) + b * s) ≤ exp (-s / (8 * D * t)) := by
-- proof
  apply exp_le_exp_of_le
  have h8Dt_pos : (0:ℝ) < 8 * D * t := by positivity
  have hbt8D : b * (8 * D * t) ≤ 1 := by
    calc b * (8 * D * t) = b * t * (8 * D) := by ring
      _ ≤ 1 / (8 * D) * (8 * D) := mul_le_mul_of_nonneg_right htb (by positivity)
      _ = 1 := by field_simp
  rw [show -s / (4 * D * t) + b * s = (-2 * s + b * s * (8 * D * t)) / (8 * D * t) from by
    field_simp; ring]
  rw [div_le_div_iff_of_pos_right h8Dt_pos]
  nlinarith [mul_nonneg hs (show 1 - b * (8 * D * t) ≥ 0 from by linarith)]

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_weighted_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_weighted_pointwise
  {n : ℕ}
  {D : ℝ}
  {a b : ℝ}
  {t : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : 0 < D)
  (ha : 0 ≤ a)
  (ht : 0 < t)
  (htb : b * t ≤ 1 / (8 * D)) :
-- imply
  heatKernel D t x * (a * exp (b * euclidNormSq x)) ≤ a * (2:ℝ) ^ ((n:ℝ)/2) * heatKernel (2*D) t x := by
-- proof
  have hK_nn : 0 ≤ heatKernel D t x := le_of_lt (heatKernel_pos hD ht x)
  have hns : 0 ≤ euclidNormSq x := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  unfold heatKernel
  set P := (4 * π * D * t) ^ ((n:ℝ)/2) with hP_def
  have hP_pos : 0 < P := by positivity
  have step1 : 1 / P * exp (-(euclidNormSq x) / (4 * D * t)) * (a * exp (b * euclidNormSq x)) =
    a / P * exp (-(euclidNormSq x) / (4 * D * t) + b * euclidNormSq x) := by
    rw [show 1 / P * exp (-(euclidNormSq x) / (4 * D * t)) * (a * exp (b * euclidNormSq x)) =
      a / P * (exp (-(euclidNormSq x) / (4 * D * t)) * exp (b * euclidNormSq x)) from by ring]
    rw [← exp_add]
  have step2 : a * (2:ℝ) ^ ((n:ℝ)/2) *
    (1 / (4 * π * (2 * D) * t) ^ ((n:ℝ)/2) * exp (-(euclidNormSq x) / (4 * (2 * D) * t))) =
    a / P * exp (-(euclidNormSq x) / (8 * D * t)) := by
    rw [show -(euclidNormSq x) / (4 * (2 * D) * t) = -(euclidNormSq x) / (8 * D * t) from by ring]
    rw [show a * (2:ℝ) ^ ((n:ℝ)/2) * (1 / (4 * π * (2 * D) * t) ^ ((n:ℝ)/2) * exp (-(euclidNormSq x) / (8 * D * t))) =
      (2:ℝ) ^ ((n:ℝ)/2) * (1 / (4 * π * (2 * D) * t) ^ ((n:ℝ)/2)) * (a * exp (-(euclidNormSq x) / (8 * D * t))) from by ring]
    rw [prefactor_identity_weighted n D t hD ht]
    ring
  rw [step1, step2]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg ha (le_of_lt hP_pos))
  exact exp_bound_weighted (euclidNormSq x) D b t hns hD ht htb

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_weighted_concentration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_weighted_concentration
  {n : ℕ}
  {D : ℝ}
  {φ : (Fin n → ℝ) → ℝ}
  {a b : ℝ}
  {δ : ℝ}
-- given
  (hD : 0 < D)
  (hφ : Continuous φ)
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hbound : ∀ x, |φ x| ≤ a * exp (b * euclidNormSq x))
  (hδ : 0 < δ) :
-- imply
  Tendsto (fun t => ∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x * |φ x|) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
-- proof
  set S := {x : Fin n → ℝ | δ < ‖x‖}
  set C := a * (2:ℝ) ^ ((n:ℝ)/2)
  have hC_nn : 0 ≤ C := mul_nonneg ha (by positivity)
  have hS_meas : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have h2D_pos : 0 < 2 * D := by positivity
  apply squeeze_zero' (f := fun t => ∫ x in S, heatKernel D t x * |φ x|)
    (g := fun t => C * ∫ x in S, heatKernel (2 * D) t x)
  · apply eventually_nhdsWithin_of_forall
    intro t ht_pos
    apply setIntegral_nonneg hS_meas (fun x _ =>
      mul_nonneg (le_of_lt (heatKernel_pos hD ht_pos x)) (abs_nonneg _))
  ·
    set t₀ := if b = 0 then (1 : ℝ) else 1 / (8 * D * b) with ht₀_def
    have ht₀_pos : 0 < t₀ := by
      simp only [ht₀_def]; split_ifs with hb0
      · exact one_pos
      · positivity
    filter_upwards [Ioo_mem_nhdsGT ht₀_pos] with t ht
    have ht_pos : 0 < t := ht.1
    have ht_lt : t < t₀ := ht.2
    have htb_bound : b * t ≤ 1 / (8 * D) := by
      by_cases hb0 : b = 0
      · simp [hb0]; positivity
      · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have : t < 1 / (8 * D * b) := by
          have : t₀ = 1 / (8 * D * b) := by simp [ht₀_def, hb0]
          linarith
        have h1 : b * t < b * (1 / (8 * D * b)) := mul_lt_mul_of_pos_left this hb_pos
        have h2 : b * (1 / (8 * D * b)) = 1 / (8 * D) := by field_simp
        linarith
    have htb_strict : b * t < 1 / (4 * D) := by
      calc b * t ≤ 1 / (8 * D) := htb_bound
        _ < 1 / (4 * D) := by
          rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 8 * D) (by positivity : (0:ℝ) < 4 * D)]
          nlinarith
    have hint_lhs : Integrable (fun x => heatKernel D t x * |φ x|) :=
      heatKernel_mul_integrable hD hφ.abs ha hb
        (fun x => by simp [abs_abs]; exact hbound x) ht_pos htb_strict
    have hint_2D : Integrable (fun x : Fin n → ℝ => heatKernel (2 * D) t x) :=
      Integrable.of_integral_ne_zero (by rw [gaussian_integral_eq_one (n := n) h2D_pos ht_pos]; exact one_ne_zero)
    have hint_rhs : Integrable (fun x => C * heatKernel (2 * D) t x) :=
      hint_2D.const_mul C
    rw [show C * ∫ x in S, heatKernel (2 * D) t x =
      ∫ x in S, C * heatKernel (2 * D) t x from
      (MeasureTheory.integral_const_mul C _).symm]
    apply setIntegral_mono hint_lhs.integrableOn hint_rhs.integrableOn
    intro x
    calc heatKernel D t x * |φ x|
      ≤ heatKernel D t x * (a * exp (b * euclidNormSq x)) :=
        mul_le_mul_of_nonneg_left (hbound x) (le_of_lt (heatKernel_pos hD ht_pos x))
      _ ≤ C * heatKernel (2 * D) t x :=
        heatKernel_weighted_pointwise hD ha ht_pos htb_bound x
  · have h_conc := heatKernel_concentration (n := n) h2D_pos δ hδ
    have : Tendsto (fun t => C * ∫ x in S, heatKernel (2 * D) t x)
      (nhdsWithin 0 (Ioi 0)) (nhds (C * 0)) :=
      h_conc.const_mul C
    simpa using this

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_ball_integral_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_ball_integral_bound
  {n : ℕ}
  {D : ℝ}
  {φ : (Fin n → ℝ) → ℝ}
  {t : ℝ}
  {ε : ℝ}
  {δ : ℝ}
-- given
  (hΓint : Integrable (fun x : Fin n → ℝ => heatKernel D t x))
  (hint_eq_one : ∫ x : Fin n → ℝ, heatKernel D t x = 1)
  (hΓpos : ∀ x : Fin n → ℝ, 0 < heatKernel D t x)
  (hε : 0 < ε)
  (hδ : 0 < δ)
  (hcont : ∀ x : Fin n → ℝ, ‖x‖ < δ → |φ x - φ 0| < ε) :
-- imply
  |∫ x in Metric.closedBall (0 : Fin n → ℝ) δ, heatKernel D t x * (φ x - φ 0)| ≤ ε := by
-- proof
  have hΓnn : ∀ x : Fin n → ℝ, 0 ≤ heatKernel D t x := fun x => le_of_lt (hΓpos x)
  have hae_eq : (Metric.closedBall (0 : Fin n → ℝ) δ : Set (Fin n → ℝ)) =ᵐ[volume]
    (Metric.ball (0 : Fin n → ℝ) δ : Set (Fin n → ℝ)) := by
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · have : Metric.closedBall (0 : Fin n → ℝ) δ \ Metric.ball (0 : Fin n → ℝ) δ =
      Metric.sphere (0 : Fin n → ℝ) δ := Metric.closedBall_diff_ball
      rw [this]; exact Measure.addHaar_sphere_of_ne_zero volume 0 hδ.ne'
    · simp [diff_eq_empty.mpr Metric.ball_subset_closedBall]
  rw [setIntegral_congr_set hae_eq]
  have hpw : ∀ x ∈ Metric.ball (0 : Fin n → ℝ) δ,
    ‖heatKernel D t x * (φ x - φ 0)‖ ≤ heatKernel D t x * ε := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hΓpos x)]
    exact mul_le_mul_of_nonneg_left (le_of_lt (hcont x hx)) (hΓnn x)
  have hΓint_on : IntegrableOn (fun x => heatKernel D t x * ε)
    (Metric.ball (0 : Fin n → ℝ) δ) :=
    hΓint.integrableOn.mul_const ε
  have h1 : ‖∫ x in Metric.ball (0 : Fin n → ℝ) δ,
    heatKernel D t x * (φ x - φ 0)‖ ≤
    ∫ x in Metric.ball (0 : Fin n → ℝ) δ, heatKernel D t x * ε := by
    apply norm_integral_le_of_norm_le hΓint_on
    exact (ae_restrict_mem measurableSet_ball).mono (fun x hx => hpw x hx)
  have h2 : ∫ x in Metric.ball (0 : Fin n → ℝ) δ,
    heatKernel D t x * ε ≤ ε := by
    calc ∫ x in Metric.ball (0 : Fin n → ℝ) δ, heatKernel D t x * ε
      ≤ ∫ x, heatKernel D t x * ε := by
        apply setIntegral_le_integral (hΓint.mul_const ε)
        exact Eventually.of_forall (fun x => mul_nonneg (hΓnn x) (le_of_lt hε))
      _ = (∫ x, heatKernel D t x) * ε := integral_mul_const ε _
      _ = 1 * ε := by rw [hint_eq_one]
      _ = ε := one_mul ε
  rw [Real.norm_eq_abs] at h1
  linarith

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_compl_integral_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_compl_integral_bound
  {n : ℕ}
  {D : ℝ}
  {φ : (Fin n → ℝ) → ℝ}
  {t : ℝ}
  {δ : ℝ}
-- given
  (hΓint : Integrable (fun x : Fin n → ℝ => heatKernel D t x))
  (hΓφ : Integrable (fun x : Fin n → ℝ => heatKernel D t x * φ x))
  (hΓpos : ∀ x : Fin n → ℝ, 0 < heatKernel D t x)
  (_hδ : 0 < δ) :
-- imply
  |∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x * (φ x - φ 0)| ≤ |φ 0| * (∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x) + ∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x * |φ x| := by
-- proof
  set S := {x : Fin n → ℝ | δ < ‖x‖}
  have hΓle : ∀ x : Fin n → ℝ, 0 ≤ heatKernel D t x := fun x => le_of_lt (hΓpos x)
  have hΓabsφ : Integrable (fun x => heatKernel D t x * |φ x|) := by
    have : (fun x => heatKernel D t x * |φ x|) = (fun x => |heatKernel D t x * φ x|) := by
      ext x; rw [abs_mul, abs_of_pos (hΓpos x)]
    rw [this]; exact hΓφ.abs
  have hΓφ_sub : Integrable (fun x => heatKernel D t x * (φ x - φ 0)) := by
    have : (fun x : Fin n → ℝ => heatKernel D t x * (φ x - φ 0)) =
      (fun x => heatKernel D t x * φ x) - (fun x => heatKernel D t x * φ 0) := by
      ext x; simp [mul_sub]
    rw [this]; exact hΓφ.sub (hΓint.mul_const _)
  have h1 : |∫ x in S, heatKernel D t x * (φ x - φ 0)| ≤
    ∫ x in S, (heatKernel D t x * |φ x| + heatKernel D t x * |φ 0|) := by
    calc |∫ x in S, heatKernel D t x * (φ x - φ 0)|
      ≤ ∫ x in S, ‖heatKernel D t x * (φ x - φ 0)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ x in S, (heatKernel D t x * |φ x| + heatKernel D t x * |φ 0|) := by
        apply setIntegral_mono hΓφ_sub.norm.integrableOn
          (hΓabsφ.integrableOn.add (hΓint.mul_const _).integrableOn)
        intro x
        show ‖heatKernel D t x * (φ x - φ 0)‖ ≤
          heatKernel D t x * |φ x| + heatKernel D t x * |φ 0|
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hΓpos x)]
        calc heatKernel D t x * |φ x - φ 0|
          ≤ heatKernel D t x * (|φ x| + |φ 0|) :=
            mul_le_mul_of_nonneg_left (abs_sub (φ x) (φ 0)) (hΓle x)
          _ = heatKernel D t x * |φ x| + heatKernel D t x * |φ 0| := by ring
  have h2 : ∫ x in S, (heatKernel D t x * |φ x| + heatKernel D t x * |φ 0|) =
    (∫ x in S, heatKernel D t x * |φ x|) + ∫ x in S, heatKernel D t x * |φ 0| :=
    integral_add hΓabsφ.integrableOn (hΓint.mul_const _).integrableOn
  have h3 : ∫ x in S, heatKernel D t x * |φ 0| = |φ 0| * ∫ x in S, heatKernel D t x := by
    have heq : (fun (x : Fin n → ℝ) => heatKernel D t x * |φ 0|) =
      (fun (x : Fin n → ℝ) => |φ 0| * heatKernel D t x) := by ext x; ring
    rw [heq]; exact integral_const_mul _ _
  linarith

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_approx_pointwise_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_approx_pointwise_bound
  {n : ℕ}
  {D : ℝ}
  {φ : (Fin n → ℝ) → ℝ}
  {a b : ℝ}
  {ε : ℝ}
  {δ : ℝ}
  {t : ℝ}
-- given
  (hD : 0 < D)
  (hφ : Continuous φ)
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hbound : ∀ x, |φ x| ≤ a * exp (b * euclidNormSq x))
  (hε : 0 < ε)
  (hδ : 0 < δ)
  (hcont : ∀ x : Fin n → ℝ, ‖x‖ < δ → |φ x - φ 0| < ε)
  (ht : 0 < t)
  (htb : b * t < 1 / (4 * D)) :
-- imply
  |(∫ x, heatKernel D t x * φ x) - φ 0| ≤ ε + |φ 0| * (∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x) + ∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x * |φ x| := by
-- proof
  have hΓφ : Integrable (fun x : Fin n → ℝ => heatKernel D t x * φ x) :=
    heatKernel_mul_integrable hD hφ ha hb hbound ht htb
  have hint_eq_one := gaussian_integral_eq_one (n := n) hD ht
  have hΓint : Integrable (fun x : Fin n → ℝ => heatKernel D t x) :=
    Integrable.of_integral_ne_zero (by rw [hint_eq_one]; exact one_ne_zero)
  have hΓpos : ∀ x : Fin n → ℝ, 0 < heatKernel D t x := heatKernel_pos hD ht
  have hΓdiff : Integrable (fun x : Fin n → ℝ => heatKernel D t x * (φ x - φ 0)) := by
    have : (fun x => heatKernel D t x * (φ x - φ 0)) =
      (fun x => heatKernel D t x * φ x - heatKernel D t x * φ 0) := by ext x; ring
    rw [this]; exact hΓφ.sub (hΓint.mul_const _)
  have hrewrite : (∫ x, heatKernel D t x * φ x) - φ 0 =
    ∫ x, heatKernel D t x * (φ x - φ 0) := by
    have h1 : φ 0 = ∫ x : Fin n → ℝ, heatKernel D t x * φ 0 := by
      conv_rhs =>
        rw [show (fun x : Fin n → ℝ => heatKernel D t x * φ 0) =
          (fun x => (φ 0) * heatKernel D t x) from by ext; ring]
      rw [integral_const_mul, hint_eq_one, mul_one]
    have h2 : ∫ x : Fin n → ℝ, heatKernel D t x * (φ x - φ 0) =
      (∫ x, heatKernel D t x * φ x) - ∫ x : Fin n → ℝ, heatKernel D t x * φ 0 := by
      rw [← integral_sub hΓφ (hΓint.mul_const _)]
      congr 1; ext x; ring
    linarith
  rw [hrewrite]
  set S := Metric.closedBall (0 : Fin n → ℝ) δ
  have hS_meas : MeasurableSet S := measurableSet_closedBall
  have hSc_eq : Sᶜ = {x : Fin n → ℝ | δ < ‖x‖} := by
    ext x; simp [S, Metric.mem_closedBall, dist_zero_right, not_le]
  have hsplit := integral_add_compl hS_meas hΓdiff
  rw [← hsplit, hSc_eq]
  have hball := heatKernel_ball_integral_bound hΓint hint_eq_one hΓpos ε hε δ hδ hcont
  have hcompl := heatKernel_compl_integral_bound hΓint hΓφ hΓpos δ hδ (φ := φ)
  have h_tri := abs_add_le
    (∫ x in S, heatKernel D t x * (φ x - φ 0))
    (∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x * (φ x - φ 0))
  linarith

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_approx_identity_estimate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_approx_identity_estimate
  {n : ℕ}
  {D : ℝ}
  {φ : (Fin n → ℝ) → ℝ}
  {a b : ℝ}
  {ε : ℝ}
  {δ : ℝ}
-- given
  (hD : 0 < D)
  (hφ : Continuous φ)
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hbound : ∀ x, |φ x| ≤ a * exp (b * euclidNormSq x))
  (hε : 0 < ε)
  (hδ : 0 < δ)
  (hcont : ∀ x : Fin n → ℝ, ‖x‖ < δ → |φ x - φ 0| < ε) :
-- imply
  ∀ᶠ t in nhdsWithin 0 (Ioi 0), |(∫ x, heatKernel D t x * φ x) - φ 0| < 2 * ε := by
-- proof
  have h_conc := heatKernel_concentration (n := n) hD δ hδ
  have h_wconc := heatKernel_weighted_concentration hD hφ ha hb hbound δ hδ
  have h1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
    |φ 0| * (∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x) < ε / 2 := by
    by_cases hφ0 : φ 0 = 0
    · filter_upwards with t; simp [hφ0]; linarith
    · have h_abs_pos : 0 < |φ 0| := abs_pos.mpr hφ0
      rw [Metric.tendsto_nhds] at h_conc
      have hev := h_conc (ε / (2 * |φ 0|)) (by positivity)
      filter_upwards [hev] with t ht
      rw [Real.dist_eq, sub_zero] at ht
      calc |φ 0| * ∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x
        ≤ |φ 0| * |∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) h_abs_pos.le
        _ < |φ 0| * (ε / (2 * |φ 0|)) := mul_lt_mul_of_pos_left ht h_abs_pos
        _ = ε / 2 := by field_simp
  have h2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
    ∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x * |φ x| < ε / 2 := by
    rw [Metric.tendsto_nhds] at h_wconc
    have hev := h_wconc (ε / 2) (by linarith)
    filter_upwards [hev] with t ht
    rw [Real.dist_eq, sub_zero] at ht
    exact lt_of_le_of_lt (le_abs_self _) ht
  have h3 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), (0 : ℝ) < t :=
    eventually_nhdsWithin_of_forall (fun (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) => hx)
  have h4 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), b * t < 1 / (4 * D) := by
    have htarget : (0 : ℝ) < 1 / (4 * D) := by positivity
    have : ∀ᶠ t in nhds (0 : ℝ), b * t < 1 / (4 * D) := by
      have : b * (0 : ℝ) < 1 / (4 * D) := by rw [mul_zero]; exact htarget
      exact (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds this
    exact this.filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, h2, h3, h4] with t ht1 ht2 ht3 ht4
  have hpw := heatKernel_approx_pointwise_bound hD hφ ha hb hbound ε hε δ hδ hcont ht3 ht4
  linarith

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_approx_identity_inner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_approx_identity_inner
  {n : ℕ}
  {D : ℝ}
-- given
  (hD : 0 < D) :
-- imply
  ∀ (φ : (Fin n → ℝ) → ℝ), Continuous φ → ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ x, |φ x| ≤ a * exp (b * euclidNormSq x)) → Tendsto (fun t => ∫ x, heatKernel D t x * φ x) (nhdsWithin 0 (Ioi 0)) (nhds (φ 0)) := by
-- proof
  intro φ hφ_cont a b ha hb hbound
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hφ_cont_at : ContinuousAt φ 0 := hφ_cont.continuousAt
  rw [Metric.continuousAt_iff] at hφ_cont_at
  obtain ⟨δ, hδ, hcont_δ⟩ := hφ_cont_at (ε / 2) (half_pos hε)
  have hest := heatKernel_approx_identity_estimate hD hφ_cont ha hb hbound (ε / 2) (half_pos hε) δ hδ
    (fun x hx => by
      have h1 : dist x 0 < δ := by simpa [dist_zero_right] using hx
      have h2 := hcont_δ h1
      rwa [Real.dist_eq] at h2)
  filter_upwards [hest] with t ht
  rw [Real.dist_eq]
  linarith

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_approx_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_approx_identity
  {n : ℕ}
  {D : ℝ}
  {φ : (Fin n → ℝ) → ℝ}
  {a b : ℝ}
-- given
  (hD : D > 0)
  (hφ_cont : Continuous φ)
  (ha : a ≥ 0)
  (hb : b ≥ 0)
  (hφ_bound : ∀ x, ‖φ x‖ ≤ a * Real.exp (b * ‖x‖^2)) :
-- imply
  Filter.Tendsto (fun t => ∫ x, heatKernel D t x * φ x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ 0)) := by
-- proof
  apply heatKernel_approx_identity_inner hD φ hφ_cont a b ha hb
  intro x
  have hbnd := hφ_bound x
  rw [Real.norm_eq_abs] at hbnd
  calc |φ x| ≤ a * Real.exp (b * ‖x‖ ^ 2) := hbnd
    _ ≤ a * Real.exp (b * euclidNormSq x) := by
      apply mul_le_mul_of_nonneg_left _ ha
      apply Real.exp_le_exp_of_le
      exact mul_le_mul_of_nonneg_left (norm_sq_le_euclidNormSq x) hb

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_properties](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_properties
  {n : ℕ}
  {D : ℝ}
-- given
  (hD : 0 < D) :
-- imply
  (∀ t > 0, ∀ x : Fin n → ℝ, 0 < heatKernel D t x) ∧ (∀ t > 0, ∫ x : Fin n → ℝ, heatKernel D t x = 1) ∧ (∀ δ > 0, Tendsto (fun t => ∫ x in {x : Fin n → ℝ | δ < ‖x‖}, heatKernel D t x) (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧ (∀ t > 0, ∀ x : Fin n → ℝ, heatOperator D (fun s (y : Fin n → ℝ) => heatKernel D s y) t x = 0) ∧ (∀ (φ : (Fin n → ℝ) → ℝ), Continuous φ → ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ x, |φ x| ≤ a * exp (b * euclidNormSq x)) → Tendsto (fun t => ∫ x, heatKernel D t x * φ x) (nhdsWithin 0 (Ioi 0)) (nhds (φ 0))) :=
-- proof
  ⟨fun _ ht x => heatKernel_pos hD ht x,
    fun _ ht => heatKernel_integral_one hD ht,
    fun _ hδ => heatKernel_concentration hD _ hδ,
    fun _ ht x => heatKernel_solves_heat hD ht x,
    heatKernel_approx_identity_inner hD⟩

end HeatFundamental

namespace HeatFundamental

/--
[leibniz_integral_rule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma leibniz_integral_rule
  {I : ℝ → ℝ → ℝ}
  {b₀ : ℝ}
  {s : Set ℝ}
  {bound : ℝ → ℝ}
  {bound_int : Integrable bound volume}
-- given
  (hI_int : ∀ᶠ b in nhds b₀, Integrable (fun a => I a b) (volume : Measure ℝ))
  (hs : s ∈ nhds b₀)
  (hI_meas : ∀ b ∈ s, AEStronglyMeasurable (fun a => I a b) volume)
  (hI'_meas : ∀ b ∈ s, AEStronglyMeasurable (fun a => deriv (fun b' => I a b') b) volume)
  (h_bound : ∀ᵐ (a : ℝ), ∀ b ∈ s, ‖deriv (fun b' => I a b') b‖ ≤ bound a)
  (h_diff : ∀ᵐ (a : ℝ), ∀ b ∈ s, HasDerivAt (fun b' => I a b') (deriv (fun b' => I a b') b) b) :
-- imply
  ∀ᶠ b in nhds b₀, HasDerivAt (fun b => ∫ a, I a b) (∫ a, deriv (fun b' => I a b') b) b := by
-- proof
  filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs), hI_int]
    with b hb_int_s hb_integrable
  have hs_b : s ∈ nhds b :=
    mem_nhds_iff.mpr ⟨interior s, interior_subset, isOpen_interior, hb_int_s⟩
  have hI_meas_b : ∀ᶠ b' in nhds b, AEStronglyMeasurable (fun a => I a b') volume :=
    Filter.eventually_of_mem hs_b (fun b' hb' => hI_meas b' hb')
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_b hI_meas_b hb_integrable
    (hI'_meas b (interior_subset hb_int_s)) h_bound bound_int h_diff).2

end HeatFundamental

namespace HeatFundamental

/--
[laplacian_const_mul'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma laplacian_const_mul'
  {n : ℕ}
  {A : ℝ}
  {f : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ} :
-- imply
  laplacian (fun y => A * f y) x = A * laplacian f x := by
-- proof
  unfold laplacian
  simp_rw [show (fun y => A * f y) = (A • f) from by ext z; simp [Pi.smul_apply, smul_eq_mul]]
  simp_rw [fderiv_const_smul_field (𝕜 := ℝ) A]
  simp only [Pi.smul_apply, ContinuousLinearMap.coe_smul', smul_eq_mul]
  simp_rw [show ∀ i : Fin n, (fun y => A * (fderiv ℝ f y) (Pi.single i 1)) =
    A • (fun y => (fderiv ℝ f y) (Pi.single i 1)) from
    fun i => by ext z; simp [Pi.smul_apply, smul_eq_mul]]
  simp_rw [fderiv_const_smul_field (𝕜 := ℝ) A]
  simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

end HeatFundamental

namespace HeatFundamental

/--
[laplacian_translate'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma laplacian_translate'
  {n : ℕ}
  {f : (Fin n → ℝ) → ℝ}
  {x₀ x : Fin n → ℝ} :
-- imply
  laplacian (fun y => f (y - x₀)) x = laplacian f (x - x₀) := by
-- proof
  unfold laplacian
  congr 1; ext i
  simp_rw [fderiv_comp_sub x₀]
  exact congr_arg (· (Pi.single i 1))
    (@fderiv_comp_sub ℝ _ _ _ _ ℝ _ _ (fun y => (fderiv ℝ f y) (Pi.single i 1)) x x₀)

end HeatFundamental

namespace HeatFundamental

/--
[laplacian_smul'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma laplacian_smul'
  {n : ℕ}
  {f : (Fin n → ℝ) → ℝ}
  {l : ℝ}
  {x : Fin n → ℝ} :
-- imply
  laplacian (fun y => f (l • y)) x = l ^ 2 * laplacian f (l • x) := by
-- proof
  unfold laplacian
  rw [Finset.mul_sum]; congr 1; ext i
  simp_rw [fderiv_comp_smul (𝕜 := ℝ) l]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  have eq1 : (fun y => l * (fderiv ℝ f (l • y)) (Pi.single i 1)) =
    l • (fun y => (fderiv ℝ f (l • y)) (Pi.single i 1)) := by
    ext z; simp [Pi.smul_apply, smul_eq_mul]
  rw [eq1, fderiv_const_smul_field (𝕜 := ℝ) l]
  simp only [Pi.smul_apply]
  have eq2 : fderiv ℝ (fun y => (fderiv ℝ f (l • y)) (Pi.single i 1)) x =
    l • fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i 1)) (l • x) :=
    @fderiv_comp_smul ℝ _ _ _ _ ℝ _ _ (fun y => (fderiv ℝ f y) (Pi.single i 1)) x l
  rw [eq2]; simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]; ring

end HeatFundamental

namespace HeatFundamental

/--
[heat_invariance_translation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heat_invariance_translation
  {n : ℕ}
  {D : ℝ}
  {u : ℝ → (Fin n → ℝ) → ℝ}
  {A : ℝ}
  {t₀ : ℝ}
  {x₀ : Fin n → ℝ}
-- given
  (_hD : 0 < D)
  (hu : ∀ t, ∀ x : Fin n → ℝ, heatOperator D u t x = 0) :
-- imply
  ∀ t > 0, ∀ x : Fin n → ℝ, heatOperator D (fun s y => A * u (s - t₀) (y - x₀)) t x = 0 := by
-- proof
  intro t _ht x
  unfold heatOperator
  have htime : deriv (fun s => A * u (s - t₀) (x - x₀)) t =
    A * deriv (fun s => u s (x - x₀)) (t - t₀) := by
    rw [show (fun s => A * u (s - t₀) (x - x₀)) =
      (fun s => A * ((fun s' => u s' (x - x₀)) (s - t₀))) from rfl]
    rw [deriv_const_mul_field A]
    congr 1
    exact deriv_comp_sub_const (fun s => u s (x - x₀)) t₀ t
  rw [htime, laplacian_const_mul' A, laplacian_translate']
  have h := hu (t - t₀) (x - x₀)
  unfold heatOperator at h
  linear_combination A * h

end HeatFundamental

namespace HeatFundamental

/--
[heat_invariance_parabolic_dilation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heat_invariance_parabolic_dilation
  {n : ℕ}
  {D : ℝ}
  {u : ℝ → (Fin n → ℝ) → ℝ}
  {A : ℝ}
  {l : ℝ}
-- given
  (_hD : 0 < D)
  (hu : ∀ t > 0, ∀ x : Fin n → ℝ, heatOperator D u t x = 0)
  (hl : 0 < l) :
-- imply
  ∀ t > 0, ∀ x : Fin n → ℝ, heatOperator D (fun s y => A * u (l ^ 2 * s) (l • y)) t x = 0 := by
-- proof
  intro t ht x
  unfold heatOperator
  have htime : deriv (fun s => A * u (l ^ 2 * s) (l • x)) t =
    A * (l ^ 2 * deriv (fun s => u s (l • x)) (l ^ 2 * t)) := by
    rw [show (fun s => A * u (l ^ 2 * s) (l • x)) =
      (fun s => A * (fun s' => u s' (l • x)) (l ^ 2 * s)) from rfl]
    rw [deriv_const_mul_field A]
    congr 1
    have := @deriv_comp_mul_left ℝ ℝ _ _ _ (l ^ 2) (fun s => u s (l • x)) t
    simp [smul_eq_mul] at this
    exact this
  rw [htime, laplacian_const_mul' A, laplacian_smul']
  have hl2t : l ^ 2 * t > 0 := mul_pos (sq_pos_of_pos hl) ht
  have h := hu (l ^ 2 * t) hl2t (l • x)
  unfold heatOperator at h
  linear_combination A * l ^ 2 * h

end HeatFundamental

namespace HeatFundamental

/--
[euclidNormSq_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma euclidNormSq_nonneg
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  0 ≤ euclidNormSq x :=
-- proof
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

end HeatFundamental

namespace HeatFundamental

/--
[euclidNormSq_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma euclidNormSq_sub_le
  {n : ℕ}
  {x z : Fin n → ℝ} :
-- imply
  euclidNormSq (x - z) ≤ 2 * euclidNormSq x + 2 * euclidNormSq z := by
-- proof
  unfold euclidNormSq
  simp only [Pi.sub_apply]
  have h : ∀ i : Fin n, (x i - z i) ^ 2 ≤ 2 * (x i) ^ 2 + 2 * (z i) ^ 2 := by
    intro i; nlinarith [sq_nonneg (x i - z i), sq_nonneg (x i + z i)]
  calc ∑ i, (x i - z i) ^ 2
    ≤ ∑ i, (2 * (x i) ^ 2 + 2 * (z i) ^ 2) := Finset.sum_le_sum (fun i _ => h i)
    _ = 2 * ∑ i, (x i) ^ 2 + 2 * ∑ i, (z i) ^ 2 := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum]

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_nonneg_pos_time](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_nonneg_pos_time
  {n : ℕ}
  {D t : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  0 ≤ heatKernel D t x := by
-- proof
  unfold heatKernel
  apply mul_nonneg
  · rw [one_div]; exact inv_nonneg.mpr (rpow_nonneg (by positivity) _)
  · exact (exp_pos _).le

end HeatFundamental

namespace HeatFundamental

/--
[cauchySolution_zero_pos_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma cauchySolution_zero_pos_dim
  {n : ℕ}
  {D : ℝ}
  {g : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
-- given
  (hn : 0 < n) :
-- imply
  cauchySolution D g 0 x = 0 := by
-- proof
  unfold cauchySolution heatKernel
  simp only [mul_zero]
  have : (0 : ℝ) ^ ((n : ℝ) / 2) = 0 := by apply zero_rpow; positivity
  simp [this]

end HeatFundamental

namespace HeatFundamental

/--
[cinv_sub_b_pos_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma cinv_sub_b_pos_aux
  {c b : ℝ}
-- given
  (hc : 0 < c)
  (hcb : c * b < 1) :
-- imply
  0 < c⁻¹ - b := by
-- proof
  rw [sub_pos, inv_eq_one_div]; rwa [lt_div_iff₀ hc, mul_comm]

end HeatFundamental

namespace HeatFundamental

/--
[completing_square_identity_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma completing_square_identity_aux
  {c b a y : ℝ}
-- given
  (hc : 0 < c)
  (hcb : c * b < 1) :
-- imply
  -(a - y) ^ 2 / c + b * y ^ 2 = b / (1 - c * b) * a ^ 2 - (c⁻¹ - b) * (y - a * c⁻¹ / (c⁻¹ - b)) ^ 2 := by
-- proof
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have h1_sub_cb : (1 - c * b) ≠ 0 := ne_of_gt (by linarith)
  have hα_ne : c⁻¹ - b ≠ 0 := ne_of_gt (cinv_sub_b_pos_aux c b hc hcb)
  field_simp; ring

end HeatFundamental

namespace HeatFundamental

/--
[one_d_completing_square_integral_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma one_d_completing_square_integral_aux
  {c b a : ℝ}
-- given
  (hc : 0 < c)
  (hb : 0 < b)
  (hcb : c * b < 1) :
-- imply
  ∫ y : ℝ, (1 / (π * c) ^ ((1:ℝ)/2) * exp (-(a - y) ^ 2 / c + b * y ^ 2)) = (1 / (1 - c * b)) ^ ((1:ℝ)/2) * exp (b / (1 - c * b) * a ^ 2) := by
-- proof
  have h1_sub_cb : 0 < 1 - c * b := by linarith
  have hα_pos := cinv_sub_b_pos_aux c b hc hcb
  have hπc_pos : 0 < π * c := by positivity
  set K := b / (1 - c * b) * a ^ 2; set α := c⁻¹ - b; set s := a * c⁻¹ / α
  have hfun_eq : (fun y => 1 / (π * c) ^ ((1:ℝ)/2) * exp (-(a - y) ^ 2 / c + b * y ^ 2)) =
    fun y => (1 / (π * c) ^ ((1:ℝ)/2) * exp K) * exp (-(α * (y - s) ^ 2)) := by
    ext y; simp only [K, α, s]
    rw [completing_square_identity_aux c b a y hc hcb,
      show b / (1 - c * b) * a ^ 2 - (c⁻¹ - b) * (y - a * c⁻¹ / (c⁻¹ - b)) ^ 2 =
        b / (1 - c * b) * a ^ 2 + (-((c⁻¹ - b) * (y - a * c⁻¹ / (c⁻¹ - b)) ^ 2)) from by ring,
      exp_add]; ring
  rw [hfun_eq, integral_const_mul,
    show (∫ y, exp (-(α * (y - s) ^ 2))) = ∫ y, exp (-(α * y ^ 2)) from
      integral_sub_right_eq_self (fun y => exp (-(α * y ^ 2))) s,
    show (fun y => exp (-(α * y ^ 2))) = fun y => rexp (-α * y ^ 2) from by ext; congr 1; ring,
    integral_gaussian α, Real.sqrt_eq_rpow]
  have hπα : π / α = π * c / (1 - c * b) := by
    have : α = (1 - c * b) / c := by simp only [α]; field_simp [ne_of_gt hc]
    rw [this]; field_simp [ne_of_gt h1_sub_cb]
  rw [hπα, show π * c / (1 - c * b) = π * c * (1 / (1 - c * b)) from by ring,
    mul_rpow (le_of_lt hπc_pos) (le_of_lt (by positivity : (0:ℝ) < 1/(1 - c*b))),
    show 1 / (1 - c * b) = (1 - c * b)⁻¹ from one_div _]
  simp only [K]
  have h := ne_of_gt (rpow_pos_of_pos hπc_pos ((1:ℝ)/2))
  field_simp
set_option maxHeartbeats 400000 in

end HeatFundamental

namespace HeatFundamental

/--
[heatKernel_exp_prod_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heatKernel_exp_prod_aux
  {n : ℕ}
  {D t b : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t) :
-- imply
  (fun y => heatKernel D t (x - y) * exp (b * euclidNormSq y)) = fun y => ∏ i : Fin n, (1 / (π * (4 * D * t)) ^ ((1:ℝ)/2) * exp (-(x i - y i) ^ 2 / (4 * D * t) + b * (y i) ^ 2)) := by
-- proof
  ext y; unfold heatKernel euclidNormSq; simp only [Pi.sub_apply]
  have h4piDt_pos : 0 < 4 * π * D * t := by positivity
  rw [mul_assoc, ← exp_add,
    show -(∑ i : Fin n, (x i - y i) ^ 2) / (4 * D * t) + b * ∑ i : Fin n, y i ^ 2 =
      ∑ i : Fin n, (-(x i - y i) ^ 2 / (4 * D * t) + b * y i ^ 2) from by
      simp only [neg_div, Finset.sum_div, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_add_distrib.symm,
    exp_sum,
    show 1 / (4 * π * D * t) ^ ((↑n : ℝ) / 2) = (1 / (π * (4 * D * t)) ^ ((1:ℝ)/2)) ^ n from by
      rw [div_pow, one_pow]; congr 1; rw [show π * (4 * D * t) = 4 * π * D * t from by ring,
        ← rpow_natCast ((4 * π * D * t) ^ ((1:ℝ)/2)) n, ← rpow_mul (le_of_lt h4piDt_pos)]
      congr 1; ring,
    show (1 / (π * (4 * D * t)) ^ ((1:ℝ)/2)) ^ n = ∏ _i : Fin n,
      (1 / (π * (4 * D * t)) ^ ((1:ℝ)/2)) from by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
  exact Finset.prod_mul_distrib.symm
set_option maxHeartbeats 800000 in

end HeatFundamental

namespace HeatFundamental

/--
[gaussian_nD_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma gaussian_nD_integral_eq
  {n : ℕ}
  {D t b : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : 0 < D)
  (ht : 0 < t)
  (hb : 0 < b)
  (hcb : 4 * D * t * b < 1) :
-- imply
  ∫ y : Fin n → ℝ, heatKernel D t (x - y) * exp (b * euclidNormSq y) = (1 / (1 - 4 * D * t * b)) ^ ((n : ℝ) / 2) * exp (b / (1 - 4 * D * t * b) * euclidNormSq x) := by
-- proof
  set c := 4 * D * t
  have hc_pos : 0 < c := by positivity
  have hcb' : c * b < 1 := by linarith
  have h1_sub_cb_pos : 0 < 1 - c * b := by linarith
  rw [heatKernel_exp_prod_aux D t b hD ht x,
    MeasureTheory.integral_fintype_prod_volume_eq_prod
      (fun i s => 1 / (π * c) ^ ((1:ℝ)/2) * exp (-(x i - s) ^ 2 / c + b * s ^ 2))]
  simp_rw [one_d_completing_square_integral_aux c b _ hc_pos hb hcb']
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  · rw [← rpow_natCast, ← rpow_mul (le_of_lt (div_pos one_pos h1_sub_cb_pos))]; congr 1; ring
  · rw [← exp_sum]; congr 1; simp only [euclidNormSq, ← Finset.mul_sum]
set_option maxHeartbeats 800000 in

end HeatFundamental

namespace HeatFundamental

/--
[gaussian_integral_completing_square](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma gaussian_integral_completing_square
  {n : ℕ}
  {D : ℝ}
  {b : ℝ}
  {t T' : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : 0 < D)
  (hb : 0 < b)
  (ht : 0 < t)
  (htT' : t ≤ T')
  (hT'bound : T' < 1 / (4 * D * b)) :
-- imply
  ∫ y : Fin n → ℝ, heatKernel D t (x - y) * exp (b * euclidNormSq y) ≤ (1 / (1 - 4 * D * T' * b)) ^ ((n : ℝ) / 2) * exp (b / (1 - 4 * D * T' * b) * euclidNormSq x) := by
-- proof
  have hDb : 0 < 4 * D * b := by positivity
  have h4DT'b_lt : 4 * D * T' * b < 1 := by
    rw [show 4 * D * T' * b = T' * (4 * D * b) from by ring]
    rwa [lt_div_iff₀ hDb] at hT'bound
  have h4Dtb_lt : 4 * D * t * b < 1 := by nlinarith [htT']
  have h1_t : 0 < 1 - 4 * D * t * b := by linarith
  have h1_T' : 0 < 1 - 4 * D * T' * b := by linarith
  rw [gaussian_nD_integral_eq D t b hD ht hb h4Dtb_lt x]
  have hmono : 1 - 4 * D * T' * b ≤ 1 - 4 * D * t * b := by nlinarith [htT']
  have hmono_coeff : 1 / (1 - 4 * D * t * b) ≤ 1 / (1 - 4 * D * T' * b) :=
    div_le_div_of_nonneg_left (le_of_lt one_pos) h1_T' hmono
  have hmono_coeff_T_pos : 0 < 1 / (1 - 4 * D * T' * b) := div_pos one_pos h1_T'
  apply mul_le_mul
  · exact rpow_le_rpow (le_of_lt (div_pos one_pos h1_t)) hmono_coeff (by positivity)
  · apply exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (euclidNormSq_nonneg x)
    exact div_le_div_of_nonneg_left (le_of_lt hb) h1_T' hmono
  · exact le_of_lt (exp_pos _)
  · exact le_of_lt (rpow_pos_of_pos hmono_coeff_T_pos _)

end HeatFundamental

namespace HeatFundamental

/--
[integrable_majorant_heatKernel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma integrable_majorant_heatKernel
  {n : ℕ}
  {D : ℝ}
  {a : ℝ}
  {b : ℝ}
  {t : ℝ}
  {x : Fin n → ℝ}
-- given
  (hD : 0 < D)
  (hb : 0 < b)
  (ht : 0 < t)
  (htb : t < 1 / (4 * D * b)) :
-- imply
  Integrable (fun y => a * exp (b * euclidNormSq y) * heatKernel D t (x - y)) := by
-- proof
  have h4Dtb : 4 * D * t * b < 1 := by
    rw [show 4 * D * t * b = t * (4 * D * b) from by ring]
    rwa [lt_div_iff₀ (by positivity : (0:ℝ) < 4 * D * b)] at htb
  suffices h : Integrable (fun y => heatKernel D t (x - y) * exp (b * euclidNormSq y)) by
    have : (fun y => a * exp (b * euclidNormSq y) * heatKernel D t (x - y)) =
      fun y => a * (heatKernel D t (x - y) * exp (b * euclidNormSq y)) := by ext; ring
    rw [this]; exact h.const_mul a
  exact Integrable.of_integral_ne_zero (by
    rw [gaussian_nD_integral_eq D t b hD ht hb h4Dtb x]
    apply mul_ne_zero
    · exact ne_of_gt (rpow_pos_of_pos (div_pos one_pos (by linarith)) _)
    · exact ne_of_gt (exp_pos _))

end HeatFundamental

namespace HeatFundamental

/--
[gaussian_convolution_uniform_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma gaussian_convolution_uniform_bound
  {n : ℕ}
  {D : ℝ}
  {g : (Fin n → ℝ) → ℝ}
  {a : ℝ}
  {b : ℝ}
  {T' : ℝ}
-- given
  (hD : 0 < D)
  (hg_cont : Continuous g)
  (ha : 0 < a)
  (hb : 0 < b)
  (hg_bound : ∀ x, |g x| ≤ a * exp (b * euclidNormSq x))
  (hT' : 0 < T')
  (hT'bound : T' < 1 / (4 * D * b)) :
-- imply
  ∀ t x, 0 ≤ t → t ≤ T' → |cauchySolution D g t x| ≤ a * (1 / (1 - 4 * D * T' * b)) ^ ((n : ℝ) / 2) * exp (b / (1 - 4 * D * T' * b) * euclidNormSq x) := by
-- proof
  intro t x ht htT'
  have hDb : 0 < 4 * D * b := by positivity
  have hc : 0 < 1 - 4 * D * T' * b := by
    nlinarith [show T' * (4 * D * b) < 1 from by rwa [lt_div_iff₀ hDb] at hT'bound]
  obtain rfl | ht_pos := eq_or_lt_of_le ht
  ·
    obtain rfl | hn := Nat.eq_zero_or_pos n
    ·
      simp only [euclidNormSq, Finset.univ_eq_empty, Finset.sum_empty,
        Nat.cast_zero, zero_div, rpow_zero, mul_one, mul_zero, exp_zero]
      unfold cauchySolution
      have hK : ∀ z : Fin 0 → ℝ, heatKernel D 0 z = 1 := by
        intro z; simp [heatKernel, euclidNormSq]
      simp_rw [hK, mul_one]
      have hga : ∀ z : Fin 0 → ℝ, |g z| ≤ a := by
        intro z; have := hg_bound z; simp [euclidNormSq] at this; exact this
      calc |∫ y : Fin 0 → ℝ, g y|
        = ‖∫ y : Fin 0 → ℝ, g y‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ y : Fin 0 → ℝ, ‖g y‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ _ : Fin 0 → ℝ, a := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ (fun y => norm_nonneg _)
          · exact integrable_const _
          · exact ae_of_all _ (fun y => by dsimp; exact hga y)
        _ = a := by
          rw [integral_const]
          have : (volume : Measure (Fin 0 → ℝ)) univ = 1 := Measure.pi_empty_univ _
          simp [Measure.real, this]
    ·
      rw [cauchySolution_zero_pos_dim hn, abs_zero]
      apply mul_nonneg
      · apply mul_nonneg ha.le; exact rpow_nonneg (by positivity) _
      · exact (exp_pos _).le
  ·
    unfold cauchySolution
    have htb : t < 1 / (4 * D * b) := lt_of_le_of_lt htT' hT'bound
    rw [show |∫ y, g y * heatKernel D t (x - y)|
      = ‖∫ y, g y * heatKernel D t (x - y)‖ from (Real.norm_eq_abs _).symm]
    calc ‖∫ y, g y * heatKernel D t (x - y)‖
      ≤ ∫ y, ‖g y * heatKernel D t (x - y)‖ := norm_integral_le_integral_norm _
      _ = ∫ y, |g y| * heatKernel D t (x - y) := by
        congr 1; ext y
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (heatKernel_nonneg_pos_time hD ht_pos (x - y))]
      _ ≤ ∫ y, a * exp (b * euclidNormSq y) * heatKernel D t (x - y) := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun y =>
          mul_nonneg (abs_nonneg _) (heatKernel_nonneg_pos_time hD ht_pos _))
        · exact integrable_majorant_heatKernel hD hb ht_pos htb x
        · exact ae_of_all _ (fun y =>
          mul_le_mul_of_nonneg_right (hg_bound y)
            (heatKernel_nonneg_pos_time hD ht_pos (x - y)))
      _ = a * ∫ y, exp (b * euclidNormSq y) * heatKernel D t (x - y) := by
        rw [← integral_const_mul]; congr 1; ext y; ring
      _ ≤ a * ((1 / (1 - 4 * D * T' * b)) ^ ((n : ℝ) / 2) *
        exp (b / (1 - 4 * D * T' * b) * euclidNormSq x)) := by
        apply mul_le_mul_of_nonneg_left _ ha.le
        rw [show ∫ y : Fin n → ℝ, exp (b * euclidNormSq y) * heatKernel D t (x - y) =
          ∫ y : Fin n → ℝ, heatKernel D t (x - y) * exp (b * euclidNormSq y) from by
          congr 1; ext y; ring]
        exact gaussian_integral_completing_square hD hb ht_pos htT' hT'bound x
      _ = a * (1 / (1 - 4 * D * T' * b)) ^ ((n : ℝ) / 2) *
        exp (b / (1 - 4 * D * T' * b) * euclidNormSq x) := by ring

end HeatFundamental

namespace HeatFundamental

/--
[gaussian_integral_growth_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma gaussian_integral_growth_bound
  {n : ℕ}
  {D : ℝ}
  {g : (Fin n → ℝ) → ℝ}
  {a : ℝ}
  {b : ℝ}
-- given
  (hD : 0 < D)
  (hg_cont : Continuous g)
  (ha : 0 < a)
  (hb : 0 < b)
  (hg_bound : ∀ x, |g x| ≤ a * exp (b * euclidNormSq x)) :
-- imply
  ∀ T' : ℝ, 0 < T' → T' < 1 / (4 * D * b) → ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t x, 0 ≤ t → t ≤ T' → |cauchySolution D g t x| ≤ A * exp (B * euclidNormSq x) := by
-- proof
  intro T' hT' hT'bound
  have hDb : 0 < 4 * D * b := by positivity
  have hc : 0 < 1 - 4 * D * T' * b := by
    nlinarith [show T' * (4 * D * b) < 1 from by rwa [lt_div_iff₀ hDb] at hT'bound]
  exact ⟨a * (1 / (1 - 4 * D * T' * b)) ^ ((n : ℝ) / 2),
    b / (1 - 4 * D * T' * b),
    by positivity, by positivity,
    gaussian_convolution_uniform_bound hD hg_cont ha hb hg_bound hT' hT'bound⟩

end HeatFundamental

namespace HeatFundamental

/--
[cauchy_solution_growth_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma cauchy_solution_growth_bound
  {n : ℕ}
  {D : ℝ}
  {g : (Fin n → ℝ) → ℝ}
  {a : ℝ}
  {b : ℝ}
-- given
  (hD : 0 < D)
  (hg_cont : Continuous g)
  (ha : 0 < a)
  (hb : 0 < b)
  (hg_bound : ∀ x, |g x| ≤ a * exp (b * euclidNormSq x)) :
-- imply
  ∀ T' : ℝ, 0 < T' → T' < 1 / (4 * D * b) → ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t x, 0 ≤ t → t ≤ T' → |cauchySolution D g t x| ≤ A * exp (B * euclidNormSq x) :=
-- proof
  gaussian_integral_growth_bound hD hg_cont ha hb hg_bound

end HeatFundamental

namespace HeatFundamental

/--
[cauchy_convolution_change_of_var](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma cauchy_convolution_change_of_var
  {n : ℕ}
  {D : ℝ}
  {g : (Fin n → ℝ) → ℝ}
  {t : ℝ}
  {x : Fin n → ℝ} :
-- imply
  (∫ y, g y * heatKernel D t (x - y)) = ∫ z, heatKernel D t z * g (x - z) := by
-- proof
  have : (fun y => g y * heatKernel D t (x - y)) =
    (fun y => (fun z => heatKernel D t z * g (x - z)) (x - y)) := by
    ext y; simp [sub_sub_cancel]; ring
  rw [this]
  exact integral_sub_left_eq_self (fun z => heatKernel D t z * g (x - z))
    (MeasureTheory.MeasureSpace.volume) x

end HeatFundamental

namespace HeatFundamental

/--
[translated_growth_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma translated_growth_bound
  {n : ℕ}
  {g : (Fin n → ℝ) → ℝ}
  {a : ℝ}
  {b : ℝ}
  {x : Fin n → ℝ}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hg_bound : ∀ x, |g x| ≤ a * exp (b * euclidNormSq x)) :
-- imply
  ∃ (a' : ℝ) (b' : ℝ), 0 ≤ a' ∧ 0 ≤ b' ∧ ∀ z, |g (x - z)| ≤ a' * exp (b' * euclidNormSq z) := by
-- proof
  refine ⟨a * exp (2 * b * euclidNormSq x), 2 * b, ?_, ?_, ?_⟩
  · exact mul_nonneg (le_of_lt ha) (le_of_lt (exp_pos _))
  · linarith
  · intro z
    have h1 : |g (x - z)| ≤ a * exp (b * euclidNormSq (x - z)) := hg_bound (x - z)
    have h2 : euclidNormSq (x - z) ≤ 2 * euclidNormSq x + 2 * euclidNormSq z :=
      euclidNormSq_sub_le x z
    have h3 : b * euclidNormSq (x - z) ≤ b * (2 * euclidNormSq x + 2 * euclidNormSq z) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hb)
    have h4 : exp (b * euclidNormSq (x - z)) ≤
      exp (b * (2 * euclidNormSq x + 2 * euclidNormSq z)) :=
      exp_le_exp.mpr h3
    have h5 : b * (2 * euclidNormSq x + 2 * euclidNormSq z) =
      2 * b * euclidNormSq x + 2 * b * euclidNormSq z := by ring
    calc |g (x - z)| ≤ a * exp (b * euclidNormSq (x - z)) := h1
      _ ≤ a * exp (b * (2 * euclidNormSq x + 2 * euclidNormSq z)) :=
        mul_le_mul_of_nonneg_left h4 (le_of_lt ha)
      _ = a * exp (2 * b * euclidNormSq x + 2 * b * euclidNormSq z) := by rw [h5]
      _ = a * (exp (2 * b * euclidNormSq x) * exp (2 * b * euclidNormSq z)) := by
        rw [exp_add]
      _ = a * exp (2 * b * euclidNormSq x) * exp (2 * b * euclidNormSq z) := by ring

end HeatFundamental

namespace HeatFundamental

/--
[heat_cauchy_initial_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heat_cauchy_initial_condition
  {n : ℕ}
  {D : ℝ}
  {g : (Fin n → ℝ) → ℝ}
  {a : ℝ}
  {b : ℝ}
-- given
  (hD : 0 < D)
  (hg_cont : Continuous g)
  (ha : 0 < a)
  (hb : 0 < b)
  (hg_bound : ∀ x, |g x| ≤ a * exp (b * euclidNormSq x)) :
-- imply
  ∀ x : Fin n → ℝ, Tendsto (fun t => cauchySolution D g t x) (nhdsWithin 0 (Ioi 0)) (nhds (g x)) := by
-- proof
  intro x
  have h_eq : (fun t => cauchySolution D g t x) =
    (fun t => ∫ z, heatKernel D t z * g (x - z)) := by
    ext t; exact cauchy_convolution_change_of_var t x
  rw [h_eq]
  have hφ_cont : Continuous (fun z => g (x - z)) :=
    hg_cont.comp (continuous_const.sub continuous_id)
  obtain ⟨a', b', ha', hb', hbound'⟩ := translated_growth_bound ha hb hg_bound x
  have h_limit := heatKernel_approx_identity_inner hD (fun z => g (x - z)) hφ_cont a' b' ha' hb' hbound'
  simp only [sub_zero] at h_limit
  exact h_limit

end HeatFundamental

namespace HeatFundamental

/--
[heat_cauchy_growth_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean)
-/
@[path]
lemma heat_cauchy_growth_bound
  {n : ℕ}
  {D : ℝ}
  {g : (Fin n → ℝ) → ℝ}
  {a : ℝ}
  {b : ℝ}
-- given
  (hD : 0 < D)
  (hg_cont : Continuous g)
  (ha : 0 < a)
  (hb : 0 < b)
  (hg_bound : ∀ x, |g x| ≤ a * exp (b * euclidNormSq x)) :
-- imply
  ∀ T' : ℝ, 0 < T' → T' < 1 / (4 * D * b) → ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t x, 0 ≤ t → t ≤ T' → |cauchySolution D g t x| ≤ A * exp (B * euclidNormSq x) :=
-- proof
  cauchy_solution_growth_bound hD hg_cont ha hb hg_bound
/-- Uniqueness part of Theorem 1.1: any other solution $v$ of the heat equation matching
the initial data $g$ and satisfying a Gaussian growth bound $|v(t, x)| \le A \exp(B|x|^2)$
must coincide with the Cauchy convolution solution on $(0, 1/(4Db)) \times \mathbb R^n$. -/
end HeatFundamental



-- created on 2026-10-23
