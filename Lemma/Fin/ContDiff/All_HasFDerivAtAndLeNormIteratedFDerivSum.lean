import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private abbrev ev {n : ℕ} (j : Fin n) : Fin n → ℝ := Pi.single j 1

private noncomputable def trunc {n : ℕ} (h : Fin n → ℝ) (k : ℕ) : Fin n → ℝ := fun i => if (i : ℕ) < k then h i else 0

private lemma trunc_zero {n : ℕ} (h : Fin n → ℝ) : trunc h 0 = 0 := by
  funext i
  simp [trunc]

private lemma trunc_self {n : ℕ} (h : Fin n → ℝ) : trunc h n = h := by
  funext i
  simp [trunc, i.isLt]

private lemma trunc_succ {n : ℕ} (h : Fin n → ℝ) (j : Fin n) : trunc h ((j : ℕ) + 1) = trunc h j + h j • ev j := by
  funext i
  simp only [trunc, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  if hij : i = j then
    subst hij
    simp
  else
    have : (i : ℕ) ≠ (j : ℕ) := fun h' => hij (Fin.ext h')
    if hlt : (i : ℕ) < (j : ℕ) then
      rw [ite_eq_left (by omega), ite_eq_left hlt, ite_eq_right hij, mul_zero, add_zero]
    else
      rw [ite_eq_right (by omega), ite_eq_right hlt, ite_eq_right hij, mul_zero, add_zero]

private lemma norm_trunc_add_smul_le {n : ℕ} (h : Fin n → ℝ) (j : Fin n) (s : ℝ) (hs : |s| ≤ |h j|) : ‖trunc h j + s • ev j‖ ≤ ‖h‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg h)]
  intro i
  simp only [trunc, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Real.norm_eq_abs]
  have hi : |h i| ≤ ‖h‖ := by
    have := norm_le_pi_norm h i
    rwa [Real.norm_eq_abs] at this
  have hj : |h j| ≤ ‖h‖ := by
    have := norm_le_pi_norm h j
    rwa [Real.norm_eq_abs] at this
  if hij : i = j then
    subst hij
    simp only [lt_self_iff_false, ite_false, ite_true, zero_add, mul_one]
    exact hs.trans hj
  else
    rw [ite_eq_right hij, mul_zero, add_zero]
    split_ifs
    · exact hi
    ·
      rw [abs_zero]
      refine norm_nonneg h

private lemma hasDerivAt_line {n : ℕ} {f : (Fin n → ℝ) → ℂ} {g : Fin n → (Fin n → ℝ) → ℂ} (hfg : ∀ (t : Fin n → ℝ) (j : Fin n), HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0) (p : Fin n → ℝ) (j : Fin n) (s : ℝ) : HasDerivAt (fun s' : ℝ => f (p + s' • ev j)) (g j (p + s • ev j)) s := by
  have h0 : HasDerivAt (fun τ : ℝ => f (p + s • ev j + τ • ev j)) (g j (p + s • ev j)) 0 := hfg (p + s • ev j) j
  have hfun : (fun s' : ℝ => f (p + s' • ev j)) = fun s' => f (p + s • ev j + (s' - s) • ev j) := by
    funext s'
    congr 1
    rw [add_assoc, ← add_smul, add_sub_cancel]
  rw [hfun]
  have h0' : HasDerivAt (fun τ : ℝ => f (p + s • ev j + τ • ev j)) (g j (p + s • ev j)) (s - s) := by
    rwa [sub_self]
  refine h0'.comp_sub_const s s

private lemma norm_sub_sub_smul_le {n : ℕ} {f : (Fin n → ℝ) → ℂ} {g : Fin n → (Fin n → ℝ) → ℂ} (hfg : ∀ (t : Fin n → ℝ) (j : Fin n), HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0) (t h : Fin n → ℝ) (j : Fin n) {C : ℝ} (hC : ∀ s ∈ Set.uIcc (0 : ℝ) (h j), ‖g j (t + trunc h j + s • ev j) - g j t‖ ≤ C) : ‖f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t‖ ≤ C * |h j| := by
  set φ : ℝ → ℂ := fun s => f (t + trunc h j + s • ev j) - s • g j t with hφ
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) (h j), HasDerivWithinAt φ (g j (t + trunc h j + s • ev j) - g j t) (Set.uIcc (0 : ℝ) (h j)) s := by
    intro s _
    have h1 := hasDerivAt_line hfg (t + trunc h j) j s
    have h2 : HasDerivAt (fun s : ℝ => s • g j t) (g j t) s := by
      simpa using (hasDerivAt_id s).smul_const (g j t)
    refine (h1.sub h2).hasDerivWithinAt
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hC (convex_uIcc (0 : ℝ) (h j)) Set.left_mem_uIcc Set.right_mem_uIcc
  have hφeq : φ (h j) - φ 0 = f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t := by
    simp only [hφ, zero_smul, add_zero, sub_zero, trunc_succ, add_assoc]
    abel
  rw [← hφeq]
  simpa [Real.norm_eq_abs] using hmv

private lemma hasFDerivAt_of_partials {n : ℕ} {f : (Fin n → ℝ) → ℂ} {g : Fin n → (Fin n → ℝ) → ℂ} (hgc : ∀ j, Continuous (g j)) (hfg : ∀ (t : Fin n → ℝ) (j : Fin n), HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0) (t : Fin n → ℝ) : HasFDerivAt f (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hG : Continuous (fun p : Fin n → ℝ => fun j : Fin n => g j p) := continuous_pi fun j => hgc j
  have hc' : 0 < c / ((n : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp hG t (c / ((n : ℝ) + 1)) hc'
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  rw [dist_zero_right] at hh
  have hnear : ∀ (j : Fin n) (s : ℝ), s ∈ Set.uIcc (0 : ℝ) (h j) → ‖g j (t + trunc h j + s • ev j) - g j t‖ ≤ c / ((n : ℝ) + 1) := by
    intro j s hs
    have hs' : |s| ≤ |h j| := by simpa using Set.abs_sub_left_of_mem_uIcc hs
    have hd : dist (t + trunc h j + s • ev j) t < δ := by
      rw [dist_eq_norm, add_assoc, add_sub_cancel_left]
      exact (norm_trunc_add_smul_le h j s hs').trans_lt hh
    have hlt := hδ' _ hd
    rw [dist_eq_norm] at hlt
    have hcomp := norm_le_pi_norm ((fun j' : Fin n => g j' (t + trunc h j + s • ev j)) - fun j' => g j' t) j
    simp only [Pi.sub_apply] at hcomp
    exact hcomp.trans hlt.le
  have htel : f (t + h) - f t = ∑ j : Fin n, (f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j)) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => f (t + trunc h (k + 1)) - f (t + trunc h k)) n, Finset.sum_range_sub (fun k => f (t + trunc h k)) n, trunc_self, trunc_zero, add_zero]
  have hL : (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) h = ∑ j, h j • g j t := by
    simp [ContinuousLinearMap.smulRight_apply]
  rw [hL, htel, ← Finset.sum_sub_distrib]
  have hn : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc
    _ ≤ ∑ j : Fin n, ‖f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n, c / ((n : ℝ) + 1) * |h j| := Finset.sum_le_sum fun j _ => norm_sub_sub_smul_le hfg t h j (hnear j)
    _ ≤ ∑ j : Fin n, c / ((n : ℝ) + 1) * ‖h‖ := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hj : |h j| ≤ ‖h‖ := by
        have := norm_le_pi_norm h j
        rwa [Real.norm_eq_abs] at this
      refine mul_le_mul_of_nonneg_left hj hc'.le
    _ = c * ((n : ℝ) / ((n : ℝ) + 1)) * ‖h‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ c * 1 * ‖h‖ := by gcongr
    _ = c * ‖h‖ := by ring

private noncomputable def A {n : ℕ} (j : Fin n) : ℂ →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) ℂ (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)

private lemma A_apply {n : ℕ} (j : Fin n) (c : ℂ) : A j c = (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight c := rfl

private lemma norm_A_le {n : ℕ} (j : Fin n) : ‖A j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c => ?_
  rw [one_mul, A_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) fun v => ?_
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg c)

private lemma sum_smulRight_eq {n : ℕ} {g : Fin n → (Fin n → ℝ) → ℂ} (t : Fin n → ℝ) : (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) = ∑ j, A j (g j t) := rfl

private lemma contDiff_sum_A {n : ℕ} {g : Fin n → (Fin n → ℝ) → ℂ} {m : ℕ} (hg : ∀ j, ContDiff ℝ m (g j)) : ContDiff ℝ m (fun t => ∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) := by
  simp only [sum_smulRight_eq]
  exact ContDiff.sum fun j _ => (A j).contDiff.comp (hg j)

private lemma norm_iteratedFDeriv_sum_A_le {n : ℕ} {g : Fin n → (Fin n → ℝ) → ℂ} {m : ℕ} (hg : ∀ j, ContDiff ℝ m (g j)) {k : ℕ} (hk : k ≤ m) (t : Fin n → ℝ) : ‖iteratedFDeriv ℝ k (fun t => ∑ j, A j (g j t)) t‖ ≤ ∑ j, ‖iteratedFDeriv ℝ k (g j) t‖ := by
  have hk' : (k : WithTop ENat) ≤ (m : WithTop ENat) := by exact_mod_cast hk
  have hsum : iteratedFDeriv ℝ k (fun t => ∑ j, A j (g j t)) t = ∑ j, iteratedFDeriv ℝ k (fun t => A j (g j t)) t := by
    have := iteratedFDeriv_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin n))) (i := k) (f := fun j t => A j (g j t)) (fun j _ => ((A j).contDiff.comp (hg j)).of_le hk')
    rw [this]
    exact Finset.sum_apply (M := fun _ : Fin n → ℝ => ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin n → ℝ) ((Fin n → ℝ) →L[ℝ] ℂ)) t Finset.univ (fun j => iteratedFDeriv ℝ k (fun t => A j (g j t)))
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hcomp : iteratedFDeriv ℝ k (fun t => A j (g j t)) t = (A j).compContinuousMultilinearMap (iteratedFDeriv ℝ k (g j) t) := (A j).iteratedFDeriv_comp_left (hg j).contDiffAt hk'
  rw [hcomp]
  refine ((A j).norm_compContinuousMultilinearMap_le _).trans ?_
  have := norm_A_le j
  have h0 := norm_nonneg (iteratedFDeriv ℝ k (g j) t)
  nlinarith

/--
[PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single.lean)
-/
@[path]
private lemma main
  (n m : ℕ)
  (f : (Fin n → ℝ) → ℂ)
  (g : Fin n → (Fin n → ℝ) → ℂ)
  -- given
  (hg : ∀ j, ContDiff ℝ m (g j))
  (hfg : ∀ (t : Fin n → ℝ) (j : Fin n), HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0) :
  -- imply
  ContDiff ℝ (m + 1) f ∧ (∀ t, HasFDerivAt f (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t) ∧ ∀ k, k ≤ m → ∀ t, ‖iteratedFDeriv ℝ (k + 1) f t‖ ≤ ∑ j, ‖iteratedFDeriv ℝ k (g j) t‖ := by
  -- proof
  have hderiv : ∀ t, HasFDerivAt f (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t := hasFDerivAt_of_partials (fun j => (hg j).continuous) hfg
  refine ⟨contDiff_succ_iff_hasFDerivAt.mpr ⟨_, contDiff_sum_A hg, hderiv⟩, hderiv, ?_⟩
  intro k hk t
  have hfd : fderiv ℝ f = fun t => ∑ j, A j (g j t) := funext fun t => (hderiv t).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  refine norm_iteratedFDeriv_sum_A_le hg hk t


-- created on 2026-10-20
