import sympy.stats.markov_reward_process
import sympy.stats.iterates
import sympy.stats.lyapunov
import sympy.stats.step_size
import sympy.Basic
import Lemma.Iterates.AeTendsto.of.LyapunovFunction.Measurable.Measurable.LipschitzWith.Eq.Adapted.Any_Ge_0AndAeAll_LeNormMulMulSquare.All_AeEqCondExp_0.Adapted.Any_Ge_0AndAeAll_LeNormMulMul.Iterates
import Lemma.Iterates.AdaptedOnSamplePath.of.IteratesOfResidual
import Lemma.Iterates.Measurable.of.AdaptedOnSamplePath
import Lemma.Iterates.Any_Ge_0AndAll_LeNorm.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.IteratesOfResidual
import Lemma.Iterates.Any_Ge_0AndAll_LeNormSub_MulNormSub.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.All_Eq_Sum_Sum_SMul
import Lemma.Real.Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.Real.Any_Ge_0AndAll_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_LeNormSub_MulNormSub
import Lemma.Measure.Measurable_Apply_PiLE
import Lemma.Measure.AeEqCondExpIteratesUpdate.of.Measurable.Any_All_LeNorm.Measurable.Le
import Lemma.Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic
open Filter MeasureTheory ProbabilityTheory Finset Topology Preorder Iterates Real Measure


@[main]
private lemma main
  {d : ℕ}
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {MRP : FiniteMRP S}
  {x : ℕ → (ℕ → S × S) → EuclideanVec d}
  {x₀ z : EuclideanVec d}
  {α : ℕ → ℝ} [RobbinsMonro α]
  {F : EuclideanVec d → S × S → EuclideanVec d}
  {f : EuclideanVec d → EuclideanVec d}
  {φ : EuclideanVec d → ℝ}
  {φ' : EuclideanVec d → EuclideanVec d}
-- given
  (h₀ : IteratesOfResidual x x₀ α F)
  (h₁ : Measurable F.uncurry)
  (h₂ : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖)
  (h₃ : z = f z)
  (h₄ : ∀ w, f w = ∑ s, ∑ s', (MRP.μ s * MRP.P s s') • F w (s, s'))
  (h₅ : Measurable φ)
  (h₆ : Measurable φ')
  (h₇ : LyapunovFunction φ φ' f) :
-- imply
  ∀ᵐ ω ∂MRP.iid_samples, Tendsto (fun n => x n ω) atTop (𝓝 z) := by
-- proof
  have hP : RowStochastic MRP.P := inferInstance
  have hμ : StochasticVec MRP.μ := inferInstance
  have hα : RobbinsMonro α := inferInstance
  obtain ⟨L, hL, hf⟩ := Any_Ge_0AndAll_LeNormSub_MulNormSub.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.All_Eq_Sum_Sum_SMul h₄ h₂
  have hLip : LipschitzWith ⟨L, hL⟩ f := lipschitzWith_iff_norm_sub_le.2 hf
  have hfm : Measurable f := hLip.continuous.measurable
  obtain ⟨C₁, hC₁, hF⟩ := Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub h₂
  obtain ⟨C₂, hC₂, hf'⟩ := Any_Ge_0AndAll_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_LeNormSub_MulNormSub ⟨L, hL, hf⟩
  have hA := AdaptedOnSamplePath.of.IteratesOfResidual h₀
  have hxm := Measurable.of.AdaptedOnSamplePath hA

  let e₁ : ℕ → (ℕ → S × S) → EuclideanVec d := fun n ω => α (n - 1) • (F (x (n - 1) ω) (ω n) - f (x (n - 1) ω))
  have : IsProbabilityMeasure MRP.iid_samples := MRP.aug_chain_iid.traj_prob.prop
  have hIt : Iterates x x₀ f e₁ (fun _ _ => 0) α := by
    refine ⟨h₀.init, fun n ω => ?_⟩
    simp only [e₁, Nat.add_sub_cancel, h₀.step, add_zero, smul_sub]
    abel
  have hb : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂MRP.iid_samples, ∀ n, ‖e₁ (n + 1) ω‖ ≤ C * α n * (‖x n ω‖ + 1) := by
    refine ⟨C₁ + C₂, by positivity, ae_of_all _ fun ω n => ?_⟩
    simp only [e₁, Nat.add_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos (hα.pos n)]
    have := (hα.pos n).le
    calc _ ≤ α n * (‖F (x n ω) (ω (n + 1))‖ + ‖f (x n ω)‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) this
      _ ≤ α n * (C₁ * (‖x n ω‖ + 1) + C₂ * (‖x n ω‖ + 1)) := mul_le_mul_of_nonneg_left (add_le_add (hF _ _) (hf' _)) this
      _ = _ := by ring
  have hAd : Adapted ((Filtration.piLE (X := fun _ => S × S)).shift 1) fun n => e₁ (n + 1) := fun n => by
    simp only [e₁, Nat.add_sub_cancel]
    exact (((h₁.comp (((hxm n).mono (Filtration.piLE.mono (Nat.le_succ n)) le_rfl).prodMk (Measurable_Apply_PiLE (n + 1)))).sub (hfm.comp ((hxm n).mono (Filtration.piLE.mono (Nat.le_succ n)) le_rfl))).const_smul (α n))
  have hMDS : ∀ n, MRP.iid_samples[e₁ (n + 1) | Filtration.piLE n] =ᵐ[MRP.iid_samples] 0 := fun n => by
    obtain ⟨xn, hxnm, hxn⟩ := hA.property n
    obtain ⟨C₃, -, hC₃⟩ := Any_Ge_0AndAll_LeNorm.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.IteratesOfResidual h₀ h₂ n
    let H : EuclideanVec d × (S × S) → EuclideanVec d := fun p => α n • (F p.1 p.2 - f p.1)
    have hHm : Measurable H := (h₁.sub (hfm.comp measurable_fst)).const_smul (α n)
    have he : e₁ (n + 1) = iterates_update (Nat.le_succ n) H xn := by
      funext ω
      simp only [e₁, H, iterates_update, Nat.add_sub_cancel, hxn]
      rw [← Function.comp_apply (f := frestrictLe₂ _), frestrictLe₂_comp_frestrictLe]
    have hbdd : ∃ C, ∀ (ω : ℕ → S × S) s, ‖H (xn (frestrictLe n ω), s)‖ ≤ C := by
      refine ⟨‖α n‖ * (C₁ * (C₃ + 1) + C₂ * (C₃ + 1)), fun ω s => ?_⟩
      rw [← hxn, norm_smul]
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add ((hF _ _).trans (by gcongr; exact hC₃ ω)) ((hf' _).trans (by gcongr; exact hC₃ ω)))
    rw [he]
    apply (AeEqCondExpIteratesUpdate.of.Measurable.Any_All_LeNorm.Measurable.Le (Nat.le_succ n) hHm hbdd hxnm MRP.aug_chain_iid).trans
    refine ae_of_all _ fun ω => ?_
    have := MRP.aug_chain_iid.markov_kernel
    have hk : ∀ y : S × S, ((MRP.aug_chain_iid.kernel ^ (n + 1 - n)) (ω n)).real {y} = MRP.μ y.1 * MRP.P y.1 y.2 := fun y => by
      rw [Nat.add_sub_cancel_left, pow_one, measureReal_def]
      show ((pair_pmf MRP.μ MRP.P).toMeasure {y}).toReal = _
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y), pair_pmf, PMF.ofFintype_apply, ENNReal.toReal_ofReal (mul_nonneg (hμ.nonneg _) ((hP.stochastic _).nonneg _))]
    show ∫ s, H (xn (frestrictLe n ω), s) ∂(MRP.aug_chain_iid.kernel ^ (n + 1 - n)) (ω n) = 0
    rw [integral_fintype (Integrable.of_finite)]
    simp only [hk, H, smul_comm _ (α n), ← smul_sum, smul_sub, sum_sub_distrib, ← sum_smul, Fintype.sum_prod_type, ← h₄, Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic hP hμ, one_smul, sub_self]
  exact AeTendsto.of.LyapunovFunction.Measurable.Measurable.LipschitzWith.Eq.Adapted.Any_Ge_0AndAeAll_LeNormMulMulSquare.All_AeEqCondExp_0.Adapted.Any_Ge_0AndAeAll_LeNormMulMul.Iterates hIt hb hAd hMDS ⟨0, le_rfl, ae_of_all _ fun ω n => by simp⟩ (fun n => measurable_const) h₃ hLip h₅ h₆ h₇

-- created on 2026-09-26