import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import sympy.Basic

open MeasureTheory


/--
Bayes formula for probability densities (the continuous analogue of the event formula
`Pr(x | y) = Pr(x, y) / Pr(y)`): the conditional density of `x` given `y` equals the joint
density `Pr(x, y)` divided by the marginal density of `y`, where the marginal density is the
integral of the joint density over `x` — `Pr(y) = ∫ Pr(x, y) dx`.

The identity holds almost everywhere with respect to the product of the reference measures;
point values on the null set where the marginal density vanishes (and Radon–Nikodym
derivatives in general) carry no probabilistic information. The same statement covers
discrete random variables by taking the counting measure as the reference measure, where the
`lintegral` reduces to a sum.
-/
@[main]
private lemma main
  {Ω α β : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {ℙ : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : JointPSpace ℙ x y)
  (hx : Measurable x)
  (hy : Measurable y) :
-- imply
  (fun z : α × β ↦ JointPSpace.condDensity ℙ x y z)
    =ᵐ[ReferenceMeasure.measure.prod ReferenceMeasure.measure]
    (fun z ↦ JointPSpace.density ℙ x y z /
      lintegral ReferenceMeasure.measure (fun a ↦ JointPSpace.density ℙ x y (a, z.2))) := by
-- proof
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  have hjoint : ℙ.map (fun ω ↦ (x ω, y ω)) = (μ.prod ν).withDensity p := hjoint
  let q : β → ENNReal := fun b ↦ lintegral μ (fun a ↦ p (a, b))
  have hq : Measurable q := hp.lintegral_prod_left'
  have hmap : ℙ.map y =
      (ℙ.map (fun ω ↦ (x ω, y ω))).map Prod.snd :=
    (Measure.map_map measurable_snd
      (by fun_prop : Measurable (fun ω ↦ (x ω, y ω)))).symm
  have hlaw : ℙ.map y = ν.withDensity q := by
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
  have hm : JointPSpace.marginalDensity ℙ x y =ᵐ[ν] q := by
    show (ℙ.map y).rnDeriv ν =ᵐ[ν] q
    rw [hlaw]
    exact Measure.rnDeriv_withDensity ν hq
  have hd : JointPSpace.density ℙ x y =ᵐ[μ.prod ν] p := by
    show (ℙ.map (fun ω ↦ (x ω, y ω))).rnDeriv (μ.prod ν) =ᵐ[μ.prod ν] p
    rw [hjoint]
    exact Measure.rnDeriv_withDensity (μ.prod ν) hp
  have hswap :
      (fun z : β × α ↦ JointPSpace.density ℙ x y (z.2, z.1)) =ᵐ[ν.prod μ]
        (fun z ↦ p (z.2, z.1)) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hd
  have hsec : (fun b ↦ lintegral μ (fun a ↦ JointPSpace.density ℙ x y (a, b))) =ᵐ[ν] q :=
    (Measure.ae_ae_of_ae_prod hswap).mono fun b hb ↦ lintegral_congr_ae hb
  have hmd : (fun z ↦ JointPSpace.marginalDensity ℙ x y z.2) =ᵐ[μ.prod ν] (fun z ↦ q z.2) :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hm
  have hden :
      (fun z ↦ lintegral μ (fun a ↦ JointPSpace.density ℙ x y (a, z.2))) =ᵐ[μ.prod ν]
        (fun z ↦ q z.2) :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hsec
  unfold JointPSpace.condDensity
  exact (ae_eq_refl (fun z ↦ JointPSpace.density ℙ x y z)).div (hmd.trans hden.symm)


-- created on 2020-12-09
-- updated on 2026-09-11
