/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Compactness.DeltaGeneratedSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Def.Analysis.Calculus.Borel.Part5
/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/


namespace Real.Calculus.Borel

open scoped Topology ContDiff

lemma norm_iteratedFDeriv_g_le_gBound (a : ℕ → ℝ) (m k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (g a m) x‖ ≤ gBound a m k :=
  (Classical.choose_spec
    ((g_hasCompactSupport a m).exists_bound_iteratedFDeriv (g_contDiff a m) k)).2 k le_rfl x

lemma iteratedDeriv_g (a : ℕ → ℝ) (m k : ℕ) (x : ℝ) :
    iteratedDeriv k (g a m) x
      = coeff a m * radius a m ^ m *
          ((radius a m)⁻¹ ^ k * iteratedDeriv k (poly m) ((radius a m)⁻¹ * x)) := by
  rw [g_eq_scaled, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul ((contDiff_poly m).of_le (by exact_mod_cast le_top))]

lemma norm_iteratedFDeriv_g_le_of_lt (a : ℕ → ℝ) {k m : ℕ} (hkm : k < m) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (g a m) x‖ ≤ (1 / 2) ^ m := by
  have hR : 0 < radius a m := radius_pos a m
  have hle1 : radius a m ≤ 1 := radius_le_one a m
  have hD : ‖iteratedDeriv k (poly m) ((radius a m)⁻¹ * x)‖ ≤ polyBound m := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact norm_iteratedFDeriv_poly_le hkm.le _
  have key : radius a m ^ m * (radius a m)⁻¹ ^ k = radius a m ^ (m - k) := by
    rw [inv_pow, ← div_eq_mul_inv, eq_comm, eq_div_iff (pow_ne_zero k hR.ne'), ← pow_add,
      Nat.sub_add_cancel hkm.le]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_g]
  rw [show coeff a m * radius a m ^ m *
          ((radius a m)⁻¹ ^ k * iteratedDeriv k (poly m) ((radius a m)⁻¹ * x))
        = coeff a m * (radius a m ^ m * (radius a m)⁻¹ ^ k) *
            iteratedDeriv k (poly m) ((radius a m)⁻¹ * x) from by ring, key]
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (radius a m ^ (m - k)),
    abs_of_nonneg (pow_nonneg hR.le _)]
  calc |coeff a m| * radius a m ^ (m - k) *
        ‖iteratedDeriv k (poly m) ((radius a m)⁻¹ * x)‖
      ≤ |coeff a m| * radius a m ^ (m - k) * polyBound m := by
        apply mul_le_mul_of_nonneg_left hD
        exact mul_nonneg (abs_nonneg _) (pow_nonneg hR.le _)
    _ = |coeff a m| * polyBound m * radius a m ^ (m - k) := by ring
    _ ≤ |coeff a m| * polyBound m * radius a m := by
        apply mul_le_mul_of_nonneg_left
          (pow_le_of_le_one hR.le hle1 (Nat.sub_ne_zero_of_lt hkm))
        exact mul_nonneg (abs_nonneg _) (polyBound_nonneg m)
    _ ≤ (1 / 2) ^ m := radius_bound a m

lemma g_eventuallyEq (a : ℕ → ℝ) (m : ℕ) :
    g a m =ᶠ[𝓝 (0 : ℝ)] fun x => coeff a m * x ^ m := by
  have hcont : Continuous (fun x : ℝ => (radius a m)⁻¹ * x) := continuous_const.mul continuous_id
  have htend : Filter.Tendsto (fun x : ℝ => (radius a m)⁻¹ * x) (𝓝 0) (𝓝 0) :=
    hcont.tendsto' 0 0 (by simp)
  have h1 : ∀ᶠ x in 𝓝 (0 : ℝ), bump ((radius a m)⁻¹ * x) = 1 := by
    have := htend.eventually bump.eventuallyEq_one
    filter_upwards [this] with x hx
    simpa using hx
  filter_upwards [h1] with x hx
  simp only [g]
  rw [hx, mul_one]

lemma iteratedDeriv_g_zero (a : ℕ → ℝ) (n m : ℕ) :
    iteratedDeriv n (g a m) 0 = if n = m then a n else 0 := by
  rw [(g_eventuallyEq a m).iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · subst h
    simp only [coeff]
    have hf : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  · simp

/--
For any real sequence there exists a smooth function with prescribed jet at zero.
Source: E. Borel, Ann. Sci. Ec. Norm. Sup. (3) 12 (1895), 9-55, DOI 10.24033/asens.406.
-/
theorem borel_jet_real
    (a : ℕ → ℝ) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ n : ℕ, iteratedDeriv n f 0 = a n := by
  classical
  set v : ℕ → ℕ → ℝ := fun k m => if m ≤ k then gBound a m k else (1 / 2) ^ m with hv_def
  have hv_summable : ∀ k, Summable (v k) := by
    intro k
    have hgeo : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    rw [← summable_nat_add_iff (k + 1)]
    have heq : (fun n => v k (n + (k + 1))) = fun n => (1 / 2 : ℝ) ^ (n + (k + 1)) := by
      funext n
      simp only [hv_def]
      rw [ite_eq_right (by omega)]
    rw [heq]
    exact (summable_nat_add_iff (k + 1)).mpr hgeo
  have hbound : ∀ k m x, ‖iteratedFDeriv ℝ k (g a m) x‖ ≤ v k m := by
    intro k m x
    simp only [hv_def]
    by_cases hmk : m ≤ k
    · rw [ite_eq_left hmk]
      exact norm_iteratedFDeriv_g_le_gBound a m k x
    · rw [ite_eq_right hmk]
      exact norm_iteratedFDeriv_g_le_of_lt a (by omega) x
  refine ⟨fun x => ∑' m, g a m x, ?_, ?_⟩
  · exact contDiff_tsum (fun m => g_contDiff a m) (fun k _ => hv_summable k)
      (fun k m x _ => hbound k m x)
  · intro n
    have hsummable_fderiv : Summable (fun m => iteratedFDeriv ℝ n (g a m) 0) :=
      Summable.of_norm_bounded (hv_summable n) (fun m => hbound n m 0)
    have heq : iteratedFDeriv ℝ n (fun x => ∑' m, g a m x) 0
        = ∑' m, iteratedFDeriv ℝ n (g a m) 0 :=
      iteratedFDeriv_tsum_apply (fun m => g_contDiff a m) (fun k _ => hv_summable k)
        (fun k m x _ => hbound k m x) le_top 0
    rw [iteratedDeriv_eq_iteratedFDeriv, heq,
      ContinuousMultilinearMap.tsum_eval hsummable_fderiv]
    simp_rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_g_zero]
    rw [tsum_eq_single n (fun m hm => ite_eq_right fun h => hm h.symm), ite_eq_left rfl]

end Real.Calculus.Borel
