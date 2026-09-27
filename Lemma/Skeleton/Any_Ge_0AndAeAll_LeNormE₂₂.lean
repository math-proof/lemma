import sympy.stats.markov_samples
import sympy.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Lemma.Skeleton.G.eq.Sum_Sum_SMul
import Lemma.Skeleton.Any_Ge_0AndAll_All_LeNormG
import Lemma.Skeleton.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.Real.Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.FiniteMRP.Any_Gt_0AndLt_1AndGe_0AndAll_LeSum_AbsSubMul_Pow
import Lemma.FiniteMRP.GetPowKernelMatAugChainMarkov.eq.MulGetPowPSub_1P.of.Ge_1
import Lemma.Iterates.AdaptedOnSamplePath.of.IteratesOfResidual
import Lemma.Kernel.IntegralPow.eq.Sum_SMulPowKernelMat
import Lemma.Measure.AeEqCondExpIteratesUpdate.of.Measurable.Any_All_LeNorm.Measurable.Le
open Finset MeasureTheory Filter Real Measure Preorder


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {sk : Skeleton S d} :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂sk.mrp.markov_samples, ∀ n, ‖sk.e₂₂ (n + 1) ω‖ ≤ C * sk.anc.β n ^ 2 * (‖sk.x (sk.anc.t n) ω‖ + 1) := by
-- proof
  have hP : RowStochastic sk.mrp.P := inferInstance
  have hα : RobbinsMonro sk.α := sk.anc.hα
  obtain ⟨C₁, hC₁, hG⟩ := Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub (Skeleton.Any_Ge_0AndAll_All_LeNormSub_MulNormSub (sk := sk))
  obtain ⟨ρ, C₂, hρ0, hρ1, hC₂, hmix⟩ := FiniteMRP.Any_Gt_0AndLt_1AndGe_0AndAll_LeSum_AbsSubMul_Pow (MRP := sk.mrp)
  obtain ⟨C₃, hC₃, hsparse⟩ := sk.hanc
  have hA := Iterates.AdaptedOnSamplePath.of.IteratesOfResidual sk.hx
  have := sk.mrp.aug_chain_markov.markov_kernel
  have h1ρ : 0 < 1 - ρ := by linarith
  refine ⟨C₃ * C₂ / (1 - ρ) * C₁, by positivity, ae_all_iff.2 fun n => ?_⟩
  obtain ⟨xn, hxnm, hxn⟩ := hA.property (sk.anc.t n)
  have hcond : ∀ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)),
      sk.mrp.markov_samples[fun ω' => sk.G (sk.x (sk.anc.t n) ω') (ω' (i + 1)) | Filtration.piLE (sk.anc.t n)] =ᵐ[sk.mrp.markov_samples]
        fun ω => ∑ y, ((sk.mrp.P ^ (i - sk.anc.t n)) (ω (sk.anc.t n)).2 y.1 * sk.mrp.P y.1 y.2) • sk.G (sk.x (sk.anc.t n) ω) y := fun i hi => by
    have hi₁ := (mem_Ico.1 hi).1
    have hi' : sk.anc.t n ≤ i + 1 := by omega
    have he : (fun ω' => sk.G (sk.x (sk.anc.t n) ω') (ω' (i + 1))) = iterates_update hi' (Function.uncurry sk.G) xn := by
      funext ω
      simp only [iterates_update, Function.uncurry_apply_pair, hxn]
      rw [← Function.comp_apply (f := frestrictLe₂ _), frestrictLe₂_comp_frestrictLe]
    obtain ⟨C, -, hC⟩ := Skeleton.Any_Ge_0AndAll_All_LeNormG (sk := sk) (sk.anc.t n)
    rw [he]
    refine (AeEqCondExpIteratesUpdate.of.Measurable.Any_All_LeNorm.Measurable.Le (φ := Function.uncurry sk.G) hi' (sk.hFm.sub measurable_fst) ⟨C, fun ω s => by rw [Function.uncurry_apply_pair, ← hxn]; exact hC ω s⟩ hxnm sk.mrp.aug_chain_markov).trans (ae_of_all _ fun ω => ?_)
    show ∫ s, Function.uncurry sk.G (xn (frestrictLe (sk.anc.t n) ω), s) ∂(sk.mrp.aug_chain_markov.kernel ^ (i + 1 - sk.anc.t n)) (ω (sk.anc.t n)) = _
    rw [Kernel.IntegralPow.eq.Sum_SMulPowKernelMat]
    refine sum_congr rfl fun y _ => ?_
    rw [FiniteMRP.GetPowKernelMatAugChainMarkov.eq.MulGetPowPSub_1P.of.Ge_1 (by omega), show i + 1 - sk.anc.t n - 1 = i - sk.anc.t n by omega, Function.uncurry_apply_pair, ← hxn]
  filter_upwards [(eventually_all_finset _).2 hcond] with ω hω
  have hdiff : ∀ k, ‖∑ y, ((sk.mrp.P ^ k) (ω (sk.anc.t n)).2 y.1 * sk.mrp.P y.1 y.2) • sk.G (sk.x (sk.anc.t n) ω) y - sk.g (sk.x (sk.anc.t n) ω)‖ ≤
      C₂ * ρ ^ k * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := fun k => by
    rw [Skeleton.G.eq.Sum_Sum_SMul, Fintype.sum_prod_type, ← sum_sub_distrib]
    simp_rw [← sum_sub_distrib, ← sub_smul, ← sub_mul]
    calc _ ≤ _ := norm_sum_le _ _
      _ ≤ ∑ s, ∑ s', |(sk.mrp.P ^ k) (ω (sk.anc.t n)).2 s - sk.mrp.μ s| * sk.mrp.P s s' * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) :=
        sum_le_sum fun s _ => (norm_sum_le _ _).trans (sum_le_sum fun s' _ => by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ((hP.stochastic s).nonneg s')]
          exact mul_le_mul_of_nonneg_left (hG _ _) (mul_nonneg (abs_nonneg _) ((hP.stochastic s).nonneg s')))
      _ = (∑ s, |(sk.mrp.P ^ k) (ω (sk.anc.t n)).2 s - sk.mrp.μ s|) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by
        rw [sum_mul]
        refine sum_congr rfl fun s _ => ?_
        rw [← sum_mul, ← mul_sum, (hP.stochastic s).rowsum, mul_one]
      _ ≤ _ := by
        gcongr
        exact hmix _ k
  have hαt := hα.pos (sk.anc.t n)
  have hterm : ∀ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)),
      ‖sk.α i • (sk.mrp.markov_samples[fun ω' => sk.G (sk.x (sk.anc.t n) ω') (ω' (i + 1)) | Filtration.piLE (sk.anc.t n)] ω - sk.g (sk.x (sk.anc.t n) ω))‖ ≤
        sk.α (sk.anc.t n) * (C₂ * ρ ^ (i - sk.anc.t n) * (C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1))) := fun i hi => by
    rw [hω i hi, norm_smul, Real.norm_eq_abs, abs_of_pos (hα.pos i)]
    exact mul_le_mul (sk.anc.hα_mono (mem_Ico.1 hi).1) (hdiff _) (norm_nonneg _) hαt.le
  have hgeom : ∑ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ρ ^ (i - sk.anc.t n) ≤ 1 / (1 - ρ) := by
    rw [sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left, range_eq_Ico]
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := sk.anc.t (n + 1) - sk.anc.t n) hρ0.le hρ1
  simp only [Skeleton.e₂₂, Nat.add_sub_cancel]
  calc _ ≤ _ := norm_sum_le _ _
    _ ≤ _ := sum_le_sum hterm
    _ = sk.α (sk.anc.t n) * C₂ * C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1) * ∑ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ρ ^ (i - sk.anc.t n) := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring
    _ ≤ sk.α (sk.anc.t n) * C₂ * C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1) * (1 / (1 - ρ)) := by gcongr
    _ ≤ C₃ * sk.anc.β n ^ 2 * C₂ * C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1) * (1 / (1 - ρ)) := by
      gcongr
      exact hsparse n
    _ = _ := by ring


-- created on 2026-09-26