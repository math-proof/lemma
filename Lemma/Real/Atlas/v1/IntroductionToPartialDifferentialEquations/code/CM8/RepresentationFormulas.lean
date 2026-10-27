import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.RepresentationFormulas
open Real Set MeasureTheory CM8


namespace CM8

/--
[unitSphereArea_three](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean)
-/
@[path]
lemma unitSphereArea_three
-- imply
  unitSphereArea 3 = 4 * Real.pi := by
-- proof
  unfold unitSphereArea
  simp only [show (3 : ℕ) ≠ 0 from by omega, ↓reduceIte]
  norm_cast
  conv_lhs =>
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 from by ring]
  rw [rpow_add Real.pi_pos, rpow_one, ← Real.sqrt_eq_rpow]
  rw [show (1 : ℝ) + 1 / 2 = 1 / 2 + 1 from by ring]
  rw [Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0)]
  rw [Real.Gamma_one_half_eq]
  have hsqrt_ne : √Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp
  ring

end CM8

namespace CM8

/--
[FundSolN_eq_Phi3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean)
-/
@[path]
lemma FundSolN_eq_Phi3
-- imply
  ∀ [inst : Fact (2 ≤ 3)] (x : Fin 3 → ℝ), @FundSolN 3 inst x = Phi3 x := by
-- proof
  intro inst x
  simp only [FundSolN, show (3 : ℕ) ≠ 2 from by omega, ↓reduceIte,
    show (3 : ℕ) - 2 = 1 from by omega, pow_one]
  rw [unitSphereArea_three]
  simp only [Phi3]

end CM8

namespace CM8

/--
[FundSolN_norm_on_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean)
-/
@[path]
lemma FundSolN_norm_on_sphere
  {n : ℕ}
  [Fact (2 ≤ n)]
-- given
  (hn3 : 3 ≤ n) :
-- imply
  ∃ C_F : ℝ, 0 ≤ C_F ∧ ∀ (x : Fin n → ℝ) (ε : ℝ), 0 < ε → ∀ σ ∈ Metric.sphere x ε, ‖FundSolN (x - σ)‖ ≤ C_F / ε ^ (n - 2) := by
-- proof
  have hn2 : n ≠ 2 := by omega
  have hω_pos : 0 < unitSphereArea n := by
    unfold unitSphereArea
    rw [if_neg (by omega : n ≠ 0)]
    apply div_pos
    · exact mul_pos (by norm_num : (0:ℝ) < 2) (Real.rpow_pos_of_pos Real.pi_pos _)
    · exact Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ) / 2)
  refine ⟨1 / unitSphereArea n, by positivity, ?_⟩
  intro x ε hε σ hσ
  have hnorm_eq : ‖x - σ‖ = ε := by
    have hdist : dist σ x = ε := hσ
    rw [← hdist, dist_eq_norm, norm_sub_rev]
  have hEN_ge : ε ≤ euclidNorm (x - σ) := by
    unfold euclidNorm
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have h_norm_le : ‖x - σ‖ ≤ Real.sqrt (∑ i : Fin n, (x - σ) i ^ 2) := by
      rw [pi_norm_le_iff_of_nonempty]
      intro b
      rw [Real.norm_eq_abs]
      have h1 : (x - σ) b ^ 2 ≤ ∑ j : Fin n, (x - σ) j ^ 2 :=
        Finset.single_le_sum (f := fun j => (x - σ) j ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ b)
      calc |(x - σ) b| = Real.sqrt ((x - σ) b ^ 2) := by rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (∑ j : Fin n, (x - σ) j ^ 2) := Real.sqrt_le_sqrt h1
    linarith
  have hEN_pos : 0 < euclidNorm (x - σ) := by linarith
  have hFSN : FundSolN (x - σ) =
    -1 / (unitSphereArea n * euclidNorm (x - σ) ^ (n - 2)) := by
    unfold FundSolN; rw [if_neg hn2]
  rw [hFSN, Real.norm_eq_abs, abs_div, abs_neg, abs_one]
  have hprod_pos : 0 < unitSphereArea n * euclidNorm (x - σ) ^ (n - 2) :=
    mul_pos hω_pos (pow_pos hEN_pos _)
  rw [abs_of_pos hprod_pos, div_div]
  exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) < 1).le
    (mul_pos hω_pos (pow_pos hε _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hEN_ge _) hω_pos.le)

end CM8

namespace CM8

/--
[sup_sphere_oscillation_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean)
-/
@[path]
lemma sup_sphere_oscillation_tendsto_zero
  {n : ℕ}
  [Fact (2 ≤ n)]
  {u : (Fin n → ℝ) → ℝ}
  {Ω : Set (Fin n → ℝ)}
  {x : Fin n → ℝ}
-- given
  (hu : ContDiffOn ℝ 2 u (closure Ω))
  (hΩ : IsOpen Ω)
  (hx : x ∈ Ω) :
-- imply
  Filter.Tendsto (fun ε => ⨆ σ ∈ Metric.sphere x ε, |u σ - u x|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
-- proof
  have hcont : ContinuousAt u x :=
    hu.continuousOn.continuousAt (Filter.mem_of_superset (hΩ.mem_nhds hx) subset_closure)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη_pos, hη_bound⟩ := hcont (δ / 2) (half_pos hδ)
  refine ⟨η, hη_pos, fun ε hε_mem hε_dist => ?_⟩
  have hε_pos : (0 : ℝ) < ε := hε_mem
  have hε_lt_η : ε < η := by
    have h1 : |ε| < η := by simpa [dist_zero_right] using hε_dist
    rwa [abs_of_pos hε_pos] at h1
  have h_bound : ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| ≤ δ / 2 := by
    apply Real.iSup_le (fun σ => ?_) (le_of_lt (half_pos hδ))
    apply Real.iSup_le (fun hσ => ?_) (le_of_lt (half_pos hδ))
    have hσ_near : dist σ x < η := by
      rw [Metric.mem_sphere.mp hσ]; linarith
    have h_u_close := hη_bound hσ_near
    rw [Real.dist_eq] at h_u_close
    linarith [abs_nonneg (u σ - u x)]
  rw [dist_zero_right]
  have h_nonneg : (0 : ℝ) ≤ ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| :=
    Real.iSup_nonneg fun σ => Real.iSup_nonneg fun _ => abs_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
  linarith

end CM8

namespace CM8

/--
[surfaceIntegral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean)
-/
@[path]
lemma surfaceIntegral_eq
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {f : (Fin n → ℝ) → ℝ} :
-- imply
  surfaceIntegral Ω f = ∫ σ in frontier Ω, f σ ∂surfaceMeasure Ω :=
-- proof
  rfl

end CM8

namespace CM8

/--
[surfaceIntegral_congr_frontier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean)
-/
@[path]
lemma surfaceIntegral_congr_frontier
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {f g : (Fin n → ℝ) → ℝ}
-- given
  (h : ∀ σ ∈ frontier Ω, f σ = g σ) :
-- imply
  surfaceIntegral Ω f = surfaceIntegral Ω g := by
-- proof
  rw [surfaceIntegral_eq, surfaceIntegral_eq]
  exact setIntegral_congr_fun isClosed_frontier.measurableSet (fun σ hσ => h σ hσ)

end CM8

namespace CM8

/--
[volume_integral_G_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean)
-/
@[path]
lemma volume_integral_G_decomp
  {n : ℕ}
  [Fact (2 ≤ n)]
  {Ω : Set (Fin n → ℝ)}
  {gf : GreenFunctionN n Ω}
  {f : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
-- given
  (hPhi_int : IntegrableOn (fun y => FundSolN (x - y) * f y) Ω)
  (hcorr_int : IntegrableOn (fun y => gf.corrector x y * f y) Ω) :
-- imply
  (∫ y in Ω, f y * gf.G x y) = (∫ y in Ω, FundSolN (x - y) * f y) - (∫ y in Ω, gf.corrector x y * f y) := by
-- proof
  have h_integrand : ∀ y, f y * gf.G x y = FundSolN (x - y) * f y - gf.corrector x y * f y := by
    intro y
    rw [gf.decomposition x y]
    ring
  simp_rw [h_integrand]
  rw [MeasureTheory.integral_sub hPhi_int hcorr_int]
/-- Differentiability of $z \mapsto \Phi(x - z)$ at any point $\sigma$. -/

end CM8


-- created on 2026-10-23
