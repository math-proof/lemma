import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.RealPreimageS0.eq.Real.of.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Real.Sum_Eq.eq.One
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Real Finset


/--
Occupancy of a state `y` at time `t` expands as a finite mixture over the initial distribution:
`ℙ(s[t] = y) = ∑ x, init {x} * ∫ Kf θ (1{s = y}) t ∂(stageK θ x)` (continuous-action model, finite state space).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (y : 𝒮) :
-- imply
  (M θ).real (s t ⁻¹' {y}) =
    ∑ x, M.env.init.real {x} * ∫ z, M.Kf θ (fun z => if z.2.1 = y then (1:ℝ) else 0) t z ∂(M.stageK θ x) := by
-- proof
  have hst : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₀ t
  have h0s : Measurable (s 0) := Random.Measurable.of.All_Eq.snd.fst h₀ 0
  have hinter :
    ∫ ω, (if s t ω = y then (1:ℝ) else 0) ∂(M θ) = (M θ).real (s t ⁻¹' {y}) := by
    have hm : MeasurableSet (s t ⁻¹' {y}) := hst (measurableSet_singleton y)
    have : (fun ω => if s t ω = y then (1:ℝ) else 0) =
      Set.indicator (s t ⁻¹' {y}) (fun _ => (1:ℝ)) := by
      funext ω; simp [Set.indicator]
    rw [this, integral_indicator hm]
    change (∫ _ in s t ⁻¹' {y}, (1:ℝ) ∂(M θ)) = _
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have hsum : ∀ ω, (if s t ω = y then (1:ℝ) else 0) =
    ∑ x, (if s 0 ω = x then (1:ℝ) else 0) * (if s t ω = y then (1:ℝ) else 0) := by
    intro ω
    rw [← Finset.sum_mul, Sum_Eq.eq.One (s 0 ω), one_mul]
  have hI : ∀ x, Integrable (fun ω => (if s 0 ω = x then (1:ℝ) else 0) * (if s t ω = y then (1:ℝ) else 0)) (M θ) := by
    intro x
    have hsm :
      StronglyMeasurable (fun ω => (if s 0 ω = x then (1:ℝ) else 0) * (if s t ω = y then (1:ℝ) else 0)) :=
      ((StronglyMeasurable.of_discrete (f := fun z : 𝒮 => if z = x then (1:ℝ) else 0)).comp_measurable h0s).mul
        ((StronglyMeasurable.of_discrete (f := fun z : 𝒮 => if z = y then (1:ℝ) else 0)).comp_measurable hst)
    refine Integrable.of_bound hsm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    simp only [norm_mul]
    exact (mul_le_mul
        (by split_ifs <;> simp only [norm_one, norm_zero, le_refl, zero_le_one])
        (by split_ifs <;> simp only [norm_one, norm_zero, le_refl, zero_le_one])
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  rw [← hinter]
  have hsum' :
    (fun ω => if s t ω = y then (1:ℝ) else 0) =
      fun ω => ∑ x, (if s 0 ω = x then (1:ℝ) else 0) * (if s t ω = y then (1:ℝ) else 0) :=
    funext hsum
  rw [hsum']
  rw [integral_finsetSum _ (fun x _ => hI x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hs : s t = fun ω => (ω (0 + t)).2.1 := by
    funext ω
    rw [zero_add]
    exact (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  rw [hs, Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        h₀ (M := M) (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) θ 0 t x,
      RealPreimageS0.eq.Real.of.All_EqWithDensity h₀]


-- created on 2026-11-13
