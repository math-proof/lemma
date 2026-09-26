import sympy.stats.markov_samples
import sympy.stats.lyapunov
import sympy.stats.filtration
import sympy.Basic
import Lemma.Iterates.AeTendsto.of.LyapunovFunction.Measurable.Measurable.LipschitzWith.Eq.Adapted.Any_Ge_0AndAeAll_LeNormMulMulSquare.All_AeEqCondExp_0.Adapted.Any_Ge_0AndAeAll_LeNormMulMul.Iterates
import Lemma.Iterates.Any_Ge_0AndAll_LeNormSub_MulNormSub.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.All_Eq_Sum_Sum_SMul
import Lemma.Iterates.AdaptedOnSamplePath.of.IteratesOfResidual
import Lemma.Iterates.Measurable.of.AdaptedOnSamplePath
import Lemma.Anchors.RobbinsMonroβ
import Lemma.Anchors.StrictMonoTime
import Lemma.Real.Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.Measure.Measurable_Apply_PiLE
import Lemma.Skeleton.Iterates
import Lemma.Skeleton.IntegrableG
import Lemma.Skeleton.MeasurableG.of.Measurable.Le
import Lemma.Skeleton.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.Skeleton.Any_Ge_0AndAeAll_All_LeNormCondExp_MulAddNorm1
import Lemma.Skeleton.Any_Ge_0AndAll_All_LeNormE₂₁
import Lemma.Skeleton.Any_Ge_0AndAeAll_LeNormE₂₂
open Filter MeasureTheory Finset Topology Iterates Real Measure


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {sk : Skeleton S d}
  {z : EuclideanVec d}
  {φ : EuclideanVec d → ℝ}
  {φ' : EuclideanVec d → EuclideanVec d}
-- given
  (h₀ : z = sk.f z)
  (h₁ : Measurable φ)
  (h₂ : Measurable φ')
  (h₃ : LyapunovFunction φ φ' sk.f) :
-- imply
  ∀ᵐ ω ∂sk.mrp.markov_samples, Tendsto (fun n => sk.x (sk.anc.t n) ω) atTop (𝓝 z) := by
-- proof
  have hα : RobbinsMonro sk.α := sk.anc.hα
  have : RobbinsMonro sk.anc.β := Anchors.RobbinsMonroβ
  have : IsProbabilityMeasure sk.mrp.markov_samples := sk.mrp.aug_chain_markov.traj_prob.prop
  have hmono : Monotone sk.anc.t := Anchors.StrictMonoTime.monotone
  obtain ⟨L, hL, hf⟩ := Any_Ge_0AndAll_LeNormSub_MulNormSub.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.All_Eq_Sum_Sum_SMul sk.hfF sk.hFlip
  have hLip : LipschitzWith ⟨L, hL⟩ sk.f := lipschitzWith_iff_norm_sub_le.2 hf
  have hxm := Measurable.of.AdaptedOnSamplePath (AdaptedOnSamplePath.of.IteratesOfResidual sk.hx)
  obtain ⟨C₁, hC₁, hcondb⟩ := Skeleton.Any_Ge_0AndAeAll_All_LeNormCondExp_MulAddNorm1 (sk := sk) (μ := sk.mrp.markov_samples)
  obtain ⟨C₂, hC₂, hGb⟩ := Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub (Skeleton.Any_Ge_0AndAll_All_LeNormSub_MulNormSub (sk := sk))
  have hb₁ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂sk.mrp.markov_samples, ∀ n, ‖sk.e₁ (n + 1) ω‖ ≤ C * sk.anc.β n * (‖sk.x (sk.anc.t n) ω‖ + 1) := by
    refine ⟨C₂ + C₁, by positivity, hcondb.mono fun ω hω n => ?_⟩
    simp only [Skeleton.e₁, Nat.add_sub_cancel]
    calc _ ≤ _ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), sk.α i * ((C₂ + C₁) * (‖sk.x (sk.anc.t n) ω‖ + 1)) := sum_le_sum fun i _ => by
          have := hα.pos i
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos this]
          gcongr
          calc _ ≤ _ := norm_sub_le _ _
            _ ≤ C₂ * (‖sk.x (sk.anc.t n) ω‖ + 1) + C₁ * (‖sk.x (sk.anc.t n) ω‖ + 1) := add_le_add (hGb _ _) (hω _ _)
            _ = _ := by ring
      _ = sk.anc.β n * ((C₂ + C₁) * (‖sk.x (sk.anc.t n) ω‖ + 1)) := by rw [← sum_mul]; rfl
      _ = _ := by ring
  have hAd₁ : Adapted (((Filtration.piLE (X := fun _ : ℕ => S × S)).subsequence hmono).shift 1) fun n => sk.e₁ (n + 1) := fun n => by
    show Measurable[Filtration.piLE (sk.anc.t (n + 1))] (fun ω => sk.e₁ (n + 1) ω)
    simp only [Skeleton.e₁, Nat.add_sub_cancel]
    refine Finset.measurable_sum _ fun i hi => ?_
    have := (mem_Ico.1 hi).2
    exact ((Skeleton.MeasurableG.of.Measurable.Le (hmono (Nat.le_succ n)) ((Measurable_Apply_PiLE (X := fun _ : ℕ => S × S) (i + 1)).mono (Filtration.piLE.mono (show i + 1 ≤ sk.anc.t (n + 1) by omega)) le_rfl)).sub
      (stronglyMeasurable_condExp.measurable.mono (Filtration.piLE.mono (hmono (Nat.le_succ n))) le_rfl)).const_smul (sk.α i)
  have hAd₂ : Adapted (((Filtration.piLE (X := fun _ : ℕ => S × S)).subsequence hmono).shift 1) fun n => sk.e₂ (n + 1) := fun n => by
    show Measurable[Filtration.piLE (sk.anc.t (n + 1))] (fun ω => sk.e₂₁ (n + 1) ω + sk.e₂₂ (n + 1) ω)
    simp only [Skeleton.e₂₁, Skeleton.e₂₂, Nat.add_sub_cancel]
    refine (Finset.measurable_sum _ fun i hi => ?_).add (Finset.measurable_sum _ fun i hi => ?_)
    · have := (mem_Ico.1 hi).2
      have hj : Measurable[Filtration.piLE (sk.anc.t (n + 1))] (fun ω : ℕ → S × S => ω (i + 1)) :=
        (Measurable_Apply_PiLE (X := fun _ : ℕ => S × S) (i + 1)).mono (Filtration.piLE.mono (by omega)) le_rfl
      exact ((Skeleton.MeasurableG.of.Measurable.Le (by omega) hj).sub (Skeleton.MeasurableG.of.Measurable.Le (hmono (Nat.le_succ n)) hj)).const_smul (sk.α i)
    · exact ((stronglyMeasurable_condExp.measurable.mono (Filtration.piLE.mono (hmono (Nat.le_succ n))) le_rfl).sub
        ((hLip.continuous.measurable.sub measurable_id).comp ((hxm (sk.anc.t n)).mono (Filtration.piLE.mono (hmono (Nat.le_succ n))) le_rfl))).const_smul (sk.α i)
  have hMDS : ∀ n, sk.mrp.markov_samples[sk.e₁ (n + 1) | (Filtration.piLE (X := fun _ : ℕ => S × S)).subsequence hmono n] =ᵐ[sk.mrp.markov_samples] 0 := fun n => by
    show sk.mrp.markov_samples[sk.e₁ (n + 1) | Filtration.piLE (sk.anc.t n)] =ᵐ[sk.mrp.markov_samples] 0
    have hm : Filtration.piLE (X := fun _ : ℕ => S × S) (sk.anc.t n) ≤ MeasurableSpace.pi := Filtration.piLE.le _
    let Gi := fun i (ω' : ℕ → S × S) => sk.G (sk.x (sk.anc.t n) ω') (ω' (i + 1))
    have he : sk.e₁ (n + 1) = ∑ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), sk.α i • (Gi i - sk.mrp.markov_samples[Gi i | Filtration.piLE (sk.anc.t n)]) := by
      funext ω
      simp only [Skeleton.e₁, Nat.add_sub_cancel, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Gi]
    rw [he]
    refine (condExp_finsetSum (fun i _ => ((Skeleton.IntegrableG _ _).sub integrable_condExp).smul (sk.α i)) _).trans ?_
    have hterm : ∀ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), sk.mrp.markov_samples[sk.α i • (Gi i - sk.mrp.markov_samples[Gi i | Filtration.piLE (sk.anc.t n)]) | Filtration.piLE (sk.anc.t n)] =ᵐ[sk.mrp.markov_samples] 0 := fun i _ => by
      filter_upwards [condExp_smul (μ := sk.mrp.markov_samples) (sk.α i) (Gi i - sk.mrp.markov_samples[Gi i | Filtration.piLE (sk.anc.t n)]) (Filtration.piLE (sk.anc.t n)),
        condExp_sub (m := Filtration.piLE (sk.anc.t n)) (Skeleton.IntegrableG (sk := sk) (μ := sk.mrp.markov_samples) (sk.anc.t n) (i + 1)) (integrable_condExp (μ := sk.mrp.markov_samples) (m := Filtration.piLE (sk.anc.t n)) (f := Gi i))] with ω h₁ h₂
      rw [h₁, Pi.smul_apply, h₂, Pi.sub_apply, condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp integrable_condExp, sub_self, smul_zero, Pi.zero_apply]
    filter_upwards [(eventually_all_finset _).2 hterm] with ω hω
    rw [Finset.sum_apply, Pi.zero_apply]
    exact sum_eq_zero fun i hi => hω i hi
  have hb₂ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂sk.mrp.markov_samples, ∀ n, ‖sk.e₂ (n + 1) ω‖ ≤ C * sk.anc.β n ^ 2 * (‖sk.x (sk.anc.t n) ω‖ + 1) := by
    obtain ⟨D₁, hD₁, h21⟩ := Skeleton.Any_Ge_0AndAll_All_LeNormE₂₁ (sk := sk)
    obtain ⟨D₂, hD₂, h22⟩ := Skeleton.Any_Ge_0AndAeAll_LeNormE₂₂ (sk := sk)
    refine ⟨D₁ + D₂, by positivity, h22.mono fun ω hω n => (norm_add_le _ _).trans ?_⟩
    calc _ ≤ D₁ * sk.anc.β n ^ 2 * (‖sk.x (sk.anc.t n) ω‖ + 1) + D₂ * sk.anc.β n ^ 2 * (‖sk.x (sk.anc.t n) ω‖ + 1) := add_le_add (h21 ω n) (hω n)
      _ = _ := by ring
  exact AeTendsto.of.LyapunovFunction.Measurable.Measurable.LipschitzWith.Eq.Adapted.Any_Ge_0AndAeAll_LeNormMulMulSquare.All_AeEqCondExp_0.Adapted.Any_Ge_0AndAeAll_LeNormMulMul.Iterates
    Skeleton.Iterates hb₁ hAd₁ hMDS hb₂ hAd₂ h₀ hLip h₁ h₂ h₃


-- created on 2026-09-26