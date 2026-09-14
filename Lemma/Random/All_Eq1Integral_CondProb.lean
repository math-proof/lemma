import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
open Random MeasureTheory


@[main]
private lemma main
  {Ω α β : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace 𝕡 (x, y)) :
-- imply
  ∀ᵐ «y.bvar» ∂𝕡.map y,
    ∫⁻ «x.bvar», 𝕡.condProb (x, y) («x.bvar», «y.bvar») ∂ReferenceMeasure.measure = 1 := by
-- proof
  have := PSpace.of.PSpace_Joint.snd hP
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  let q : β → ENNReal := fun «y.bvar» ↦ lintegral μ (fun «x.bvar» ↦ p («x.bvar», «y.bvar»))
  have hq : Measurable q := hp.lintegral_prod_left'
  have hlaw : 𝕡.map y = ν.withDensity q := by
    erw [← AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hP.aemeasurable, hjoint]
    have hmarg : ν.withDensity (fun «y.bvar» ↦ lintegral μ (fun «x.bvar» ↦ p («x.bvar», «y.bvar»))) =
        ((μ.prod ν).withDensity p).snd := by
      ext s hs
      rw [withDensity_apply _ hs]
      have h : ((μ.prod ν).withDensity p).snd s =
          lintegral (ν.restrict s) (fun «y.bvar» ↦ lintegral μ (fun «x.bvar» ↦ p («x.bvar», «y.bvar»))) := by
        rw [Measure.snd_apply hs, ← Set.univ_prod,
          withDensity_apply _ (MeasurableSet.prod MeasurableSet.univ hs),
          setLIntegral_prod_symm p (hp.aemeasurable.restrict)]
        simp only [setLIntegral_univ]
      exact h.symm
    exact hmarg.symm
  have hd : 𝕡.prob (x, y) =ᵐ[μ.prod ν] p := by
    show (𝕡.map (x, y)).rnDeriv _ =ᵐ[_] p
    rw [hjoint]
    exact Measure.rnDeriv_withDensity _ hp
  have hsec :
      (fun «y.bvar» ↦ lintegral μ (fun «x.bvar» ↦ 𝕡.prob (x, y) («x.bvar», «y.bvar»))) =ᵐ[ν] q := by
    have hjp' : 𝕡.prob (x, y) =ᵐ[(ν.prod μ).map Prod.swap] p := by
      rwa [Measure.prod_swap]
    have hswap :
        (fun z : β × α ↦ 𝕡.prob (x, y) (z.2, z.1)) =ᵐ[ν.prod μ]
          fun z ↦ p (z.2, z.1) :=
      ae_eq_comp measurable_swap.aemeasurable hjp'
    exact (Measure.ae_ae_of_ae_prod hswap).mono fun _ hb ↦ lintegral_congr_ae hb
  have hm : 𝕡.prob y =ᵐ[ν] q := by
    show (𝕡.map y).rnDeriv ν =ᵐ[ν] q
    rw [hlaw]
    exact Measure.rnDeriv_withDensity ν hq
  have : IsProbabilityMeasure (𝕡.map y) :=
    Measure.isProbabilityMeasure_map PSpace.aemeasurable
  have h1 : lintegral ν q = 1 := by
    have h : (ν.withDensity q) Set.univ = lintegral ν q := by
      rw [withDensity_apply q MeasurableSet.univ, setLIntegral_univ]
    rw [← hlaw, measure_univ] at h
    exact h.symm
  have htop : ∀ᵐ «y.bvar» ∂ν, q «y.bvar» ≠ ⊤ :=
    (ae_lt_top hq (h1 ▸ ENNReal.one_ne_top)).mono fun _ hb ↦ hb.ne
  rw [hlaw, ae_withDensity_iff hq]
  filter_upwards [hsec, hm, htop] with «y.bvar» hsec_y hm_y htop_y hnz_y
  have hsec_m : Measurable (fun («x.bvar» : α) ↦ 𝕡.prob (x, y) («x.bvar», «y.bvar»)) := by
    unfold Measure.prob
    fun_prop
  show ∫⁻ «x.bvar», 𝕡.prob (x, y) («x.bvar», «y.bvar») / 𝕡.prob y «y.bvar» ∂μ = 1
  have key :
      (fun «x.bvar» : α ↦ 𝕡.prob (x, y) («x.bvar», «y.bvar») / 𝕡.prob y «y.bvar») =
        fun «x.bvar» ↦ (𝕡.prob y «y.bvar»)⁻¹ * 𝕡.prob (x, y) («x.bvar», «y.bvar») := by
    funext «x.bvar»
    rw [div_eq_mul_inv, mul_comm]
  rw [key, lintegral_const_mul'' _ hsec_m.aemeasurable, hsec_y, hm_y]
  exact ENNReal.inv_mul_cancel hnz_y htop_y


-- created on 2021-07-20
