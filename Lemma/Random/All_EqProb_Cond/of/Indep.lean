import Lemma.Random.SinglePSpace.of.IndepFun
import Lemma.Random.Map.eq.WithDensityProb
open Random MeasureTheory ProbabilityTheory


private lemma ae_map_of_ae_ref
  [MeasurableSpace Ω]
  [ReferenceMeasure γ]
  {π : Measure Ω} {z : Ω → γ} [SinglePSpace π z]
  {p : γ → Prop}
-- given
  (hp : ∀ᵐ c ∂ReferenceMeasure.measure, p c) :
-- imply
  ∀ᵐ c ∂π.map z, p c := by
-- proof
  have : π.map z ≪ (ReferenceMeasure.measure : Measure γ) := by
    rw [Map.eq.WithDensityProb (x := z) (π := π)]
    exact withDensity_absolutelyContinuous _ _
  exact this.ae_le hp

/-- Independence of `x` from `z` means the joint density factors, so
`ℙ(x | z) = ℙ(x)` almost everywhere in `x` and in `z` under `π.map z`. -/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  {π : Measure Ω}
  {x : Ω → α} [SinglePSpace π x]
  {z : Ω → γ} [SinglePSpace π z]
-- given
  (h : x ⟂ᵢ[π] z) :
-- imply
  have : SinglePSpace π (x, z) := SinglePSpace.of.IndepFun h
  ∀ᵐ «\sf{x}» ∂ReferenceMeasure.measure,
    ∀ᵐ «\sf{z}» ∂π.map z,
      ℙ[π](x = «\sf{x}» | z = «\sf{z}») = ℙ[π](x = «\sf{x}») := by
-- proof
  have : SinglePSpace π (x, z) := SinglePSpace.of.IndepFun h
  let μ : Measure α := ReferenceMeasure.measure
  let ξ : Measure γ := ReferenceMeasure.measure
  have : SigmaFinite μ := inferInstance
  have : SigmaFinite ξ := inferInstance
  have : SFinite μ := inferInstance
  have : SFinite ξ := inferInstance
  let px : α → ENNReal := π.prob x
  let pz : γ → ENNReal := π.prob z
  let pxz : α × γ → ENNReal := π.prob (x, z)
  have hpx : Measurable px := Measure.measurable_rnDeriv _ _
  have hpz : Measurable pz := Measure.measurable_rnDeriv _ _
  have hpxz : Measurable pxz := Measure.measurable_rnDeriv _ _
  have haex : AEMeasurable x π := PSpace.aemeasurable
  have haez : AEMeasurable z π := PSpace.aemeasurable
  have hindep : π.map (x, z) = (π.map x).prod (π.map z) :=
    ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map haex haez h
  have hlawx := Map.eq.WithDensityProb (x := x) (π := π)
  have hlawz := Map.eq.WithDensityProb (x := z) (π := π)
  have hprod : (μ.withDensity px).prod (ξ.withDensity pz) =
    (μ.prod ξ).withDensity (fun t ↦ px t.1 * pz t.2) :=
    prod_withDensity hpx hpz
  have hrn : pxz =ᵐ[μ.prod ξ] fun t ↦ px t.1 * pz t.2 := by
    show (π.map (x, z)).rnDeriv (μ.prod ξ) =ᵐ[μ.prod ξ] fun t ↦ px t.1 * pz t.2
    have hρ : (μ.prod ξ : Measure (α × γ)) = ReferenceMeasure.measure := rfl
    rw [hindep, hlawx, hlawz, hprod, hρ]
    exact Measure.rnDeriv_withDensity _ ((hpx.comp measurable_fst).mul (hpz.comp measurable_snd))
  have hrn_ae : ∀ᵐ a ∂μ, ∀ᵐ c ∂ξ, pxz (a, c) = px a * pz c :=
    Measure.ae_ae_of_ae_prod hrn
  have hrn_ae' : ∀ᵐ a ∂μ, ∀ᵐ c ∂π.map z, pxz (a, c) = px a * pz c := by
    filter_upwards [hrn_ae] with a ha
    exact ae_map_of_ae_ref ha
  have htotz : ∫⁻ c, pz c ∂ξ = 1 := by
    rw [← setLIntegral_univ, ← withDensity_apply (μ := ξ) (f := pz) MeasurableSet.univ,
      ← hlawz, measure_univ]
  have hpz_lt : ∀ᵐ c ∂ξ, pz c < ⊤ := ae_lt_top hpz (by rw [htotz]; norm_num)
  have hpz_lt' : ∀ᵐ c ∂π.map z, pz c < ⊤ := ae_map_of_ae_ref hpz_lt
  have hpz_ne0 : ∀ᵐ c ∂π.map z, pz c ≠ 0 := by
    have hs : MeasurableSet {c : γ | pz c = 0} := hpz (measurableSet_singleton 0)
    rw [ae_iff]
    change π.map z {c | ¬ pz c ≠ 0} = 0
    simp only [ne_eq, not_not]
    rw [hlawz, withDensity_apply _ hs]
    have heq : Set.EqOn pz (fun _ => 0) {c | pz c = 0} := fun c hc => hc
    rw [setLIntegral_congr_fun hs heq]
    simp
  have hDiv : ∀ᵐ a ∂μ, ∀ᵐ c ∂ξ, π.condProb (x, z) (a, c) = pxz (a, c) / pz c := by
    have hmapz : π.map (fun ω ↦ ((x, z) ω).2) = π.map z := by congr
    have hae : (fun t : α × γ ↦ π.condProb (x, z) t) =ᵐ[μ.prod ξ]
        (fun t ↦ π.prob (x, z) t / π.prob z t.2) := by
      filter_upwards with t
      unfold Measure.condProb Measure.prob
      rw [hmapz]
    exact Measure.ae_ae_of_ae_prod hae
  have hDiv' : ∀ᵐ a ∂μ, ∀ᵐ c ∂π.map z, π.condProb (x, z) (a, c) = pxz (a, c) / pz c := by
    filter_upwards [hDiv] with a ha
    exact ae_map_of_ae_ref ha
  filter_upwards [hDiv', hrn_ae'] with a hD hR
  filter_upwards [hD, hR, hpz_ne0, hpz_lt'] with c hDc hRc hz0 hztop
  rw [hDc, hRc, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hz0 hztop.ne, mul_one]


-- created on 2026-11-12
