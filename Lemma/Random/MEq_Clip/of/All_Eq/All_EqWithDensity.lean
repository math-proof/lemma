import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.StageKSetOf1.eq.Zero.of.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
Almost surely the reward equals the clamped reward (continuous-action model):
`r[t] =ᵐ fun ω ↦ clip (ω[t]).1 (-R) R`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  r t =ᵐ[M θ] fun ω ↦ clip (ω t).1 (-M.env.R) M.env.R := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₀ t) ω)).symm
  have hs : MeasurableSet {z : ℝ × S × A | z.1 ∉ Set.Icc (-M.env.R) M.env.R} :=
    (measurableSet_Icc.compl).preimage measurable_fst
  have h : (M θ).map (fun ω => ω t) {z | z.1 ∉ Set.Icc (-M.env.R) M.env.R} = 0 := by
    rw [Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity h₀, Measure.bind_apply hs (Kernel.aemeasurable _)]
    apply (lintegral_congr (fun y => StageKSetOf1.eq.Zero.of.All_EqWithDensity (M := M) θ y)).trans
      lintegral_zero
  rw [Measure.map_apply (measurable_pi_apply t) hs] at h
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hI
  apply hω
  unfold clip
  rw [max_eq_left hI.1, min_eq_left hI.2]


-- created on 2026-10-20
