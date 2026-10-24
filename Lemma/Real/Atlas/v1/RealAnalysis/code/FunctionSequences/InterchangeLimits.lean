import Mathlib
import sympy.Basic
open Filter Topology Set MeasureTheory intervalIntegral


/--
[uniform_limit_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/InterchangeLimits.lean)
-/
@[path]
lemma uniform_limit_derivative
  {f : ℕ → ℝ → ℝ}
  {g : ℝ → ℝ}
  {f' : ℕ → ℝ → ℝ}
  {lim : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a < b)
  (hderiv : ∀ n, ∀ x ∈ Icc a b, HasDerivAt (f n) (f' n x) x)
  (hf'_cont : ∀ n, ContinuousOn (f' n) (Icc a b))
  (hf'_unif : TendstoUniformlyOn f' g atTop (Icc a b))
  (hfg : ∀ x ∈ Icc a b, Tendsto (fun n => f n x) atTop (nhds (lim x))) :
-- imply
  (∀ x ∈ Icc a b, HasDerivWithinAt lim (g x) (Icc a b) x) ∧ ContinuousOn g (Icc a b) := by
-- proof
  have hg_cont : ContinuousOn g (Icc a b) :=
    hf'_unif.continuousOn ((Eventually.of_forall hf'_cont).frequently)
  have ha_mem : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hint_n : ∀ n, ∀ x ∈ Icc a b, IntervalIntegrable (f' n) volume a x :=
    fun n x hx => ((hf'_cont n).mono (uIcc_subset_Icc ha_mem hx)).intervalIntegrable
  have hg_int : ∀ x ∈ Icc a b, IntervalIntegrable g volume a x :=
    fun x hx => (hg_cont.mono (uIcc_subset_Icc ha_mem hx)).intervalIntegrable
  have hFTC : ∀ n, ∀ x ∈ Icc a b, f n x - f n a = ∫ t in a..x, f' n t := by
    intro n x hx
    have hderiv_uIcc : ∀ t ∈ uIcc a x, HasDerivAt (f n) (f' n t) t :=
      fun t ht => hderiv n t (uIcc_subset_Icc ha_mem hx ht)
    linarith [integral_eq_sub_of_hasDerivAt hderiv_uIcc (hint_n n x hx)]
  have hint_conv : ∀ x ∈ Icc a b,
    Tendsto (fun n => ∫ t in a..x, f' n t) atTop (nhds (∫ t in a..x, g t)) := by
    intro x hx
    have hax : a ≤ x := hx.1
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hba_pos : (0 : ℝ) < b - a + 1 := by linarith
    have hunif := Metric.tendstoUniformlyOn_iff.mp hf'_unif
      (ε / (b - a + 1)) (div_pos hε hba_pos)
    rw [Filter.eventually_atTop] at hunif
    obtain ⟨N, hN⟩ := hunif
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, ← integral_sub (hint_n n x hx) (hg_int x hx)]
    calc ‖∫ t in a..x, (f' n t - g t)‖
      ≤ ∫ t in a..x, ‖f' n t - g t‖ := norm_integral_le_integral_norm hax
      _ ≤ ∫ t in a..x, (ε / (b - a + 1)) := by
        apply integral_mono_on hax
        · exact (((hf'_cont n).sub hg_cont).mono
          (uIcc_subset_Icc ha_mem hx)).norm.intervalIntegrable
        · exact _root_.intervalIntegrable_const
        · intro t ht
          have ht_mem : t ∈ Icc a b := ⟨ht.1, le_trans ht.2 hx.2⟩
          have h := hN n hn t ht_mem
          rw [Real.dist_eq] at h
          rw [norm_sub_rev]
          exact le_of_lt h
      _ = (x - a) * (ε / (b - a + 1)) := by
        simp [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ (b - a) * (ε / (b - a + 1)) := by
        apply mul_le_mul_of_nonneg_right
        · linarith [hx.2]
        · exact le_of_lt (div_pos hε hba_pos)
      _ < ε := by
        calc (b - a) * (ε / (b - a + 1))
          < (b - a + 1) * (ε / (b - a + 1)) := by
            apply mul_lt_mul_of_pos_right (lt_add_one _) (div_pos hε hba_pos)
          _ = ε := by field_simp
  have hlim_eq : ∀ x ∈ Icc a b, lim x - lim a = ∫ t in a..x, g t := by
    intro x hx
    have h1 : Tendsto (fun n => f n x - f n a) atTop (nhds (lim x - lim a)) :=
      (hfg x hx).sub (hfg a ha_mem)
    have h2 : (fun n => f n x - f n a) = (fun n => ∫ t in a..x, f' n t) :=
      funext (fun n => hFTC n x hx)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 (hint_conv x hx)
  refine ⟨fun x hx => ?_, hg_cont⟩
  have hFTC2 : HasDerivWithinAt (fun u => ∫ t in a..u, g t) (g x) (Icc a b) x := by
    haveI : Fact (x ∈ Icc a b) := ⟨hx⟩
    exact integral_hasDerivWithinAt_right (hg_int x hx)
      (hg_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x)
      (hg_cont.continuousWithinAt hx)
  have heq : ∀ u ∈ Icc a b, lim u = lim a + ∫ t in a..u, g t := by
    intro u hu; linarith [hlim_eq u hu]
  have hFTC3 : HasDerivWithinAt (fun u => lim a + ∫ t in a..u, g t) (0 + g x) (Icc a b) x :=
    (hasDerivWithinAt_const x (Icc a b) (lim a)).add hFTC2
  rw [zero_add] at hFTC3
  exact hFTC3.congr (fun u hu => heq u hu) (heq x hx)


-- created on 2026-10-23
