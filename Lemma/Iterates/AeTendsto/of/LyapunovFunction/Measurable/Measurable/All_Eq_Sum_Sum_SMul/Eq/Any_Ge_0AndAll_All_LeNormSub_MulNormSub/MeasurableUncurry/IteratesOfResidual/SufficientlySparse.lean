import sympy.stats.markov_samples
import sympy.stats.lyapunov
import sympy.Basic
import Lemma.Skeleton.AeTendsto.of.LyapunovFunction.Measurable.Measurable.Eq
import Lemma.Iterates.Any_Ge_0AndAll_All_LeNormSub_MulSumIco_Exp.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.All_Ge_0.IteratesOfResidual
import Lemma.Anchors.RobbinsMonroβ
import Lemma.Anchors.StrictMonoTime
import Lemma.Real.Any_And_Ge_0_All_Le.of.Summable
import Lemma.Nat.Any_In_Ico.of.Eq_0.StrictMono
open Filter MeasureTheory Finset Topology Real


@[main]
private lemma main
  {d : ℕ}
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {MRP : FiniteMRP S}
  {x : ℕ → (ℕ → S × S) → EuclideanVec d}
  {x₀ z : EuclideanVec d}
  {α : ℕ → ℝ}
  {anc : Anchors α}
  {F : EuclideanVec d → S × S → EuclideanVec d}
  {f : EuclideanVec d → EuclideanVec d}
  {φ : EuclideanVec d → ℝ}
  {φ' : EuclideanVec d → EuclideanVec d}
-- given
  (h₀ : SufficientlySparse anc)
  (h₁ : IteratesOfResidual x x₀ α F)
  (h₂ : Measurable F.uncurry)
  (h₃ : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖)
  (h₄ : z = f z)
  (h₅ : ∀ w, f w = ∑ s, ∑ s', (MRP.μ s * MRP.P s s') • F w (s, s'))
  (h₆ : Measurable φ)
  (h₇ : Measurable φ')
  (h₈ : LyapunovFunction φ φ' f) :
-- imply
  ∀ᵐ ω ∂MRP.markov_samples, Tendsto (fun n => x n ω) atTop (𝓝 z) := by
-- proof
  let sk : Skeleton S d := ⟨F, h₂, h₃, f, α, anc, h₀, x, x₀, h₁, MRP, h₅⟩
  have hα : RobbinsMonro α := anc.hα
  have hβ : RobbinsMonro anc.β := Anchors.RobbinsMonroβ
  have hmono : StrictMono anc.t := Anchors.StrictMonoTime
  obtain ⟨C₁, hC₁, hgrowth⟩ := Iterates.Any_Ge_0AndAll_All_LeNormSub_MulSumIco_Exp.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.All_Ge_0.IteratesOfResidual h₁ (fun n => (hα.pos n).le) h₃
  obtain ⟨C₂, hC₂, hβC⟩ := Any_And_Ge_0_All_Le.of.Summable hβ.sqsum
  have hβ0 : Tendsto anc.β atTop (𝓝 0) := by
    have := hβ.sqsum.tendsto_atTop_zero.sqrt
    rw [Real.sqrt_zero] at this
    exact this.congr fun n => Real.sqrt_sq (hβ.pos n).le
  filter_upwards [(Skeleton.AeTendsto.of.LyapunovFunction.Measurable.Measurable.Eq (sk := sk) h₄ h₆ h₇ h₈ : ∀ᵐ ω ∂MRP.markov_samples, Tendsto (fun n => x (anc.t n) ω) atTop (𝓝 z))] with ω hω
  have hh : Tendsto (fun m => anc.β m * C₁ * (‖x (anc.t m) ω‖ + 1) * rexp (C₂ * C₁) + ‖x (anc.t m) ω - z‖) atTop (𝓝 0) := by
    simpa using (((hβ0.mul_const C₁).mul (hω.norm.add_const 1)).mul_const (rexp (C₂ * C₁))).add (tendsto_iff_norm_sub_tendsto_zero.1 hω)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hh ε hε
  refine ⟨anc.t M, fun N hN => ?_⟩
  obtain ⟨m, hm⟩ := Nat.Any_In_Ico.of.Eq_0.StrictMono hmono anc.t_zero N
  have hmM : M ≤ m := Nat.lt_succ_iff.1 (hmono.lt_iff_lt.1 (hN.trans_lt (mem_Ico.1 hm).2))
  have hg := hgrowth ω (anc.t m) (anc.t (m + 1)) N hm
  simp only [← sum_mul] at hg
  have := hβ.pos m
  rw [dist_eq_norm]
  calc ‖x N ω - z‖ ≤ ‖x N ω - x (anc.t m) ω‖ + ‖x (anc.t m) ω - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ anc.β m * C₁ * (‖x (anc.t m) ω‖ + 1) * rexp (C₂ * C₁) + ‖x (anc.t m) ω - z‖ := by
      gcongr
      refine hg.trans ?_
      show anc.β m * C₁ * (‖x (anc.t m) ω‖ + 1) * rexp (anc.β m * C₁) ≤ _
      gcongr
      exact hβC m
    _ ≤ |anc.β m * C₁ * (‖x (anc.t m) ω‖ + 1) * rexp (C₂ * C₁) + ‖x (anc.t m) ω - z‖| := le_abs_self _
    _ < ε := by
      have := hM m hmM
      rwa [Real.dist_eq, sub_zero] at this


-- created on 2026-09-26