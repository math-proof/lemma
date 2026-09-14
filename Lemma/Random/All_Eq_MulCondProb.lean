import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import Lemma.Random.All_Eq_DivProbS
open Random MeasureTheory


/--
Multiplication rule for probability densities (the continuous analogue of the event
formula `Pr(y ∧ (x = a)) = Pr(x = a | y) · Pr(y)`): the joint density equals the
conditional density of `x` given `y` times the marginal density of `y` —

  `𝕡(x, y) = 𝕡(x | y) · 𝕡(y)`

The identity holds almost everywhere with respect to the product of the reference
measures, which is exactly where `All_Eq_DivProbS` (the Bayes division formula) is valid;
the sympy premise `Pr(y) ≠ 0` is handled a.e. rather than by a hypothesis: where the
marginal density vanishes the joint density vanishes a.e. on the same fiber (a zero
section integral), and the marginal density is finite a.e. because it integrates to the
total mass `1` of the probability measure.
-/
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
  have := PSpace.of.PSpace_Joint.snd hP
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure, ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
    𝕡.prob (x, y) («x.bvar», «y.bvar») =
      𝕡.condProb (x, y) («x.bvar», «y.bvar») * 𝕡.prob y «y.bvar» := by
-- proof
  have := PSpace.of.PSpace_Joint.snd hP
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  have hjoint : 𝕡.map (x, y) = (μ.prod ν).withDensity p := hjoint
  let q : β → ENNReal := fun b ↦ lintegral μ (fun a ↦ p (a, b))
  have hq : Measurable q := hp.lintegral_prod_left'
  have hmap : 𝕡.map y =
      (𝕡.map (x, y)).map Prod.snd :=
    (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
      hP.aemeasurable).symm
  have hlaw : 𝕡.map y = ν.withDensity q := by
    rw [hmap, hjoint]
    have hmarg : ν.withDensity (fun y ↦ lintegral μ (fun x ↦ p (x, y))) =
        ((μ.prod ν).withDensity p).snd := by
      ext s hs
      rw [withDensity_apply _ hs]
      have h : ((μ.prod ν).withDensity p).snd s =
          lintegral (ν.restrict s) (fun y ↦ lintegral μ (fun x ↦ p (x, y))) := by
        rw [Measure.snd_apply hs, ← Set.univ_prod,
          withDensity_apply _ (MeasurableSet.prod MeasurableSet.univ hs),
          setLIntegral_prod_symm p (hp.aemeasurable.restrict)]
        simp only [setLIntegral_univ]
      exact h.symm
    exact hmarg.symm
  have hm : 𝕡.prob y =ᵐ[ν] q := by
    show (𝕡.map y).rnDeriv ν =ᵐ[ν] q
    rw [hlaw]
    exact Measure.rnDeriv_withDensity ν hq
  have hd : 𝕡.prob (x, y) =ᵐ[μ.prod ν] p := by
    show (𝕡.map (x, y)).rnDeriv (μ.prod ν) =ᵐ[μ.prod ν] p
    rw [hjoint]
    exact Measure.rnDeriv_withDensity (μ.prod ν) hp
  have hmd : (fun z ↦ 𝕡.prob y z.2) =ᵐ[μ.prod ν] (fun z ↦ q z.2) :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hm
  have htot : lintegral ν q = 1 := by
    have h : (ν.withDensity q) Set.univ = lintegral ν q := by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [← h, ← hlaw]
    have : IsProbabilityMeasure (𝕡.map y) :=
      Measure.isProbabilityMeasure_map (AEMeasurable.snd hP.aemeasurable)
    exact measure_univ
  have hfin : ∀ᵐ b ∂ν, q b < ⊤ :=
    ae_lt_top hq (by rw [htot]; norm_num)
  have hfinms : MeasurableSet {z : α × β | q z.2 < ⊤} :=
    (hq.comp measurable_snd) measurableSet_Iio
  have hfinp : ∀ᵐ z ∂μ.prod ν, q z.2 < ⊤ := by
    have h : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, q (a, b).2 < ⊤ := by
      filter_upwards with a
      exact hfin
    exact (Measure.ae_prod_iff_ae_ae hfinms).mpr h
  have hzero : ∀ᵐ b ∂ν, ∀ᵐ a ∂μ, q b = 0 → p (a, b) = 0 := by
    filter_upwards with b
    by_cases h0 : q b = 0
    · have hpb : Measurable (fun a : α ↦ p (a, b)) :=
        hp.comp (Measurable.prodMk measurable_id measurable_const)
      have hae : ∀ᵐ a ∂μ, p (a, b) = 0 := by
        have hq0 : lintegral μ (fun a : α ↦ p (a, b)) = 0 := h0
        exact (lintegral_eq_zero_iff hpb).mp hq0
      exact hae.mono fun a ha _ ↦ ha
    · filter_upwards with a
      exact fun h ↦ (h0 h).elim
  have h1 : MeasurableSet {z : β × α | q z.1 = 0} :=
    (hq.comp measurable_fst) (measurableSet_singleton (0 : ENNReal))
  have h2 : MeasurableSet {z : β × α | p (z.2, z.1) = 0} :=
    (hp.comp (Measurable.prodMk measurable_snd measurable_fst))
      (measurableSet_singleton (0 : ENNReal))
  have hPms : MeasurableSet {z : β × α | q z.1 = 0 → p (z.2, z.1) = 0} := by
    convert h1.compl.union h2 using 1
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union]
    exact imp_iff_not_or
  have hzero' : ∀ᵐ z ∂μ.prod ν, q z.2 = 0 → p z = 0 :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      ((Measure.ae_prod_iff_ae_ae hPms).mpr hzero)
  have hdiv : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν,
      𝕡.condProb (x, y) (a, b) = 𝕡.prob (x, y) (a, b) / 𝕡.prob y b :=
    All_Eq_DivProbS hP
  have hmp : Measurable (𝕡.prob (x, y)) := by
    simpa [Measure.prob] using Measure.measurable_rnDeriv (𝕡.map (x, y)) ReferenceMeasure.measure
  have hmy2 : Measurable (𝕡.prob y) := by
    simpa [Measure.prob] using Measure.measurable_rnDeriv (𝕡.map y) ReferenceMeasure.measure
  have hmc : Measurable (𝕡.condProb (x, y)) := by
    change Measurable (fun z : α × β ↦ 𝕡.prob (x, y) z /
      (𝕡.map (fun ω ↦ ((x, y) ω).2)).rnDeriv ReferenceMeasure.measure z.2)
    exact hmp.div ((Measure.measurable_rnDeriv (𝕡.map (fun ω ↦ ((x, y) ω).2))
      ReferenceMeasure.measure).comp measurable_snd)
  have hcdms : MeasurableSet {z : α × β | 𝕡.condProb (x, y) z = 𝕡.prob (x, y) z / 𝕡.prob y z.2} :=
    measurableSet_eq_fun hmc (hmp.div (hmy2.comp measurable_snd))
  have hcd : (fun z ↦ 𝕡.condProb (x, y) z) =ᵐ[μ.prod ν]
      (fun z ↦ 𝕡.prob (x, y) z / 𝕡.prob y z.2) :=
    (Measure.ae_prod_iff_ae_ae hcdms).mpr hdiv
  have hcancel :
      (fun z ↦ 𝕡.prob (x, y) z) =ᵐ[μ.prod ν]
        (fun z ↦ 𝕡.condProb (x, y) z * 𝕡.prob y z.2) := by
    filter_upwards [hmd, hd, hcd, hfinp, hzero'] with z hmy hpz hcdz hlt hz
    have hqz : q z.2 = 0 → p z = 0 := by
      intro hq0
      exact hz hq0
    have hpy : 𝕡.prob y z.2 = q z.2 := hmy
    have hrhs : 𝕡.condProb (x, y) z * 𝕡.prob y z.2 = (p z / q z.2) * q z.2 := by
      simp only [hcdz, hpz, hpy]
    rw [hpz, hrhs]
    exact (ENNReal.div_mul_cancel' hqz (fun h ↦ (hlt.ne h).elim)).symm
  exact Measure.ae_ae_of_ae_prod hcancel


-- created on 2020-12-09
-- updated on 2026-09-14
