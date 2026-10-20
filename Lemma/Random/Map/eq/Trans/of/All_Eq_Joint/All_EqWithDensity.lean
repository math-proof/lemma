import Lemma.Random.Map.eq.BindK.of.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Kernel


/-- `κ.comap f ∘ₘ μ = κ ∘ₘ (μ.map f)`. -/
private lemma comp_comap_eq_comp_map
  {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (κ : Kernel β γ) [IsSFiniteKernel κ] (μ : Measure α) [SFinite μ]
  {f : α → β} (hf : Measurable f) :
  κ.comap f hf ∘ₘ μ = κ ∘ₘ (μ.map f) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Kernel.comap_apply]
  exact (lintegral_map (κ.measurable_coe hs) hf).symm

/--
Next-state law under the continuous-action trajectory model:
`law(s[t+1]) = T ∘ₘ law(s[t], a[t])`.
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
  (M θ).map (s (t + 1)) =
    M.env.trans ∘ₘ (M θ).map (fun ω ↦ (s t ω, a t ω)) := by
-- proof
  have := M.env.trans_markov
  have := M.env.reward_markov
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  set μ := (M θ).map (fun ω ↦ ω t)
  have hK := Map.eq.BindK.of.All_EqWithDensity (M := M) θ t
  have hmap :
    (M θ).map (s (t + 1)) =
      ((M θ).map (fun ω ↦ ω (t + 1))).map (fun z ↦ z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply (t + 1))]; rfl
  have hsa :
    (M θ).map (fun ω ↦ (s t ω, a t ω)) = μ.map (fun z ↦ z.2) := by
    rw [Measure.map_map (measurable_snd.fst.prodMk measurable_snd.snd)
      (measurable_pi_apply t)]
    rfl
  have hsk :
    (M.stageK θ).map (fun z : ℝ × S × A => z.2.1) =
      Kernel.deterministic (id : S → S) measurable_id := by
    unfold DensityModel.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ
        (M.policy.kernel θ ⊗ₖ M.env.reward)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod _ _
  rw [hmap, hK, DensityModel.K, ← Measure.comp_assoc,
    Measure.map_comp _ _ (by fun_prop), hsk,
    Measure.deterministic_comp_eq_map, Measure.map_id, hsa,
    comp_comap_eq_comp_map]


-- created on 2026-10-20
