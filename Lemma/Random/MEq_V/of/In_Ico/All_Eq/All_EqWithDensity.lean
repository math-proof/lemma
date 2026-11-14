import Lemma.Random.MEq_V0.of.In_Ico.All_Eq.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real Filter


/--
On the trajectory law, the observation form `DensityModel.V` agrees almost
everywhere with the discounted `Wkd` series `V0`:
`V θ γ k (s k) =ᵐ V0 θ γ (s k)`.
The two may differ on a `ℙ(s[k] = x) = 0` set of states; a pointwise equality
on an atom of positive mass is
[V = V0](?module=Random.V.eq.V0.of.Ne0Real_Preimage.In_Ico).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2))
  (θ : Θ)
  (k : ℕ) :
-- imply
  (fun ω => M.V θ γ k (s k ω)) =ᵐ[M θ] (fun ω => M.V0 θ γ (s k ω)) := by
-- proof
  have hs : Measurable (s k) := Random.Measurable.of.All_Eq.snd.fst h₁ k
  have hrm : ∀ j, Measurable (r j) := fun j => Random.Measurable.of.All_Eq.fst h₁ j
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hfGret : Measurable
      (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) :=
    Measurable.tsum fun j => (measurable_pi_apply (k + j)).const_mul _
  set BV : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hr_bd : ∀ᵐ ω ∂(M θ), ∀ j, |r j ω| ≤ |M.env.R| := by
    have hcl : ∀ j, r j =ᵐ[M θ] fun ω => clip (ω j).1 (-M.env.R) M.env.R :=
      fun j => MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ j
    have hcl' : ∀ᵐ ω ∂(M θ), ∀ j,
        r j ω = clip (ω j).1 (-M.env.R) M.env.R :=
      (ae_all_iff (ι := ℕ)).mpr hcl
    filter_upwards [hcl'] with ω hω j
    rw [hω j, ← Real.norm_eq_abs]
    exact NormClip.le.Abs_R (R := M.env.R) (ρ := (ω j).1)
  have hret_bd : ∀ᵐ ω ∂(M θ),
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:])‖ ≤ BV := by
    have hgeo := (hasSum_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|
    filter_upwards [hr_bd] with ω hω
    refine tsum_of_norm_bounded hgeo fun j => ?_
    have hid : (γ ^ (id : ℕ → ℕ)) j = γ ^ j := rfl
    have hslice : (fun i => r i ω)[k:] j = r (k + j) ω := rfl
    rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hω (k + j)) (pow_nonneg hγ.1 j)
  have hret : Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] :=
    hfGret.comp hpR
  have hGi : Integrable
      (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) (M θ) :=
    Integrable.of_bound hret.aestronglyMeasurable BV
      (by filter_upwards [hret_bd] with ω hω; exact hω)
  have hV0 :=
    MEq_V0.of.In_Ico.All_Eq.All_EqWithDensity (M := M) hγ h₁ hπ θ k
  have hcomp :=
    Expectation.condEval_comp_ae_eq_condSigma
      (x := fun ω i => r i ω) (y := s k)
      (f := fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:])
      hpR.aemeasurable hs hfGret.stronglyMeasurable hGi
  have hdef : (fun ω => M.V θ γ k (s k ω)) =
      (fun ω => Expectation.condEval (M θ) (fun ω i => r i ω) (s k)
        (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) (s k ω)) := by
    obtain rfl : r = fun t ω ↦ (ω t).1 :=
      funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
    obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
      funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
    rfl
  rw [hdef]
  exact hcomp.trans hV0.symm


-- created on 2026-11-12
