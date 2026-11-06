import Lemma.Random.Expect.eq.Integral_Mul_Prob
open MeasureTheory Random


/--
Continuous importance sampling: changing the sampling law from `π` to `π'`
reweights by the likelihood ratio of densities `ℙ[π](x) / ℙ[π'](x)`
(observation / pdf form `ℙ[π](x = ·)`, not a conditional `ℙ[π](· | ·)`).
Requires the target density under `π` to vanish a.e. wherever the proposal
density under `π'` vanishes (absolute continuity of the pushforwards).
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {x : Ω → α} {f : α → ENNReal}
  {π : Measure Ω} [SinglePSpace π x]
  {π' : Measure Ω} [SinglePSpace π' x]
-- given
  (hf : Measurable f)
  (habs : ∀ᵐ «\sf{x}» ∂(ReferenceMeasure.measure : Measure α),
    ℙ[π'](x = «\sf{x}») = 0 → ℙ[π](x = «\sf{x}») = 0) :
-- imply
  𝔼[x: π](f x) = 𝔼[x: π'](f x * ℙ[π](x) / ℙ[π'](x)) := by
-- proof
  have hp : Measurable (π.prob x) := Measure.measurable_rnDeriv _ _
  have hp' : Measurable (π'.prob x) := Measure.measurable_rnDeriv _ _
  have hg : Measurable (fun «\sf{x}» ↦ f «\sf{x}» * π.prob x «\sf{x}» / π'.prob x «\sf{x}») :=
    (hf.mul hp).div hp'
  have htop : ∀ᵐ «\sf{x}» ∂(ReferenceMeasure.measure : Measure α),
      π'.prob x «\sf{x}» ≠ ⊤ :=
    Measure.rnDeriv_ne_top _ _
  rw [Expect.eq.Integral_Mul_Prob (π := π) (a := x) (f := f) inferInstance hf]
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_ennreal]
  rw [Map.eq.WithDensityProb (π := π') (x := x),
    lintegral_withDensity_eq_lintegral_mul _ hp' hg]
  refine lintegral_congr_ae ?_
  filter_upwards [habs, htop] with «\sf{x}» hs hsTop
  calc
    _ = (f «\sf{x}» * π.prob x «\sf{x}» / π'.prob x «\sf{x}») * π'.prob x «\sf{x}» :=
      (ENNReal.div_mul_cancel'
        (b := f «\sf{x}» * π.prob x «\sf{x}»)
        (fun h0 ↦ by
          have := hs h0
          simp [this])
        fun hTop ↦ (hsTop hTop).elim).symm
    _ = π'.prob x «\sf{x}» * (f «\sf{x}» * π.prob x «\sf{x}» / π'.prob x «\sf{x}») := by
      rw [mul_comm]


-- created on 2023-03-25
-- updated on 2026-11-05
