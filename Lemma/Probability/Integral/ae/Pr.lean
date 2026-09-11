import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.Basic

open MeasureTheory


private lemma marginal
  {α β : Type*}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}
  [SFinite μ] [SFinite ν]
  (p : α × β → ENNReal)
  (hp : Measurable p) :
  ν.withDensity (fun y ↦ lintegral μ (fun x ↦ p (x, y))) = ((μ.prod ν).withDensity p).snd := by
  ext s hs
  rw [withDensity_apply _ hs]
  have h : ((μ.prod ν).withDensity p).snd s =
      lintegral (ν.restrict s) (fun y ↦ lintegral μ (fun x ↦ p (x, y))) := by
    rw [Measure.snd_apply hs, ← Set.univ_prod,
      withDensity_apply _ (MeasurableSet.prod MeasurableSet.univ hs),
      setLIntegral_prod_symm p (hp.aemeasurable.restrict)]
    simp only [setLIntegral_univ]
  exact h.symm


@[main]
private lemma main
  {Ω α β : Type*}
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}
  [SFinite μ] [SigmaFinite ν]
  {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
-- given
  (x : Ω → α) (y : Ω → β)
  (hx : Measurable x) (hy : Measurable y)
  (p : α × β → ENNReal)
  (hp : Measurable p)
  (hjoint : Measure.map (fun ω ↦ (x ω, y ω)) ℙ = (μ.prod ν).withDensity p) :
-- imply
  (fun y ↦ lintegral μ (fun x ↦ p (x, y))) =ᵐ[ν] (Measure.map y ℙ).rnDeriv ν := by
-- proof
  let q := fun y : β ↦ lintegral μ (fun x ↦ p (x, y))
  have hq : Measurable q := hp.lintegral_prod_left'
  have hmap : Measure.map y ℙ =
      Measure.map Prod.snd (Measure.map (fun ω ↦ (x ω, y ω)) ℙ) :=
    (Measure.map_map measurable_snd
      (by fun_prop : Measurable (fun ω ↦ (x ω, y ω)))).symm
  have hlaw : Measure.map y ℙ = ν.withDensity q := by
    rw [hmap, hjoint]
    exact (marginal p hp).symm
  rw [hlaw]
  exact (Measure.rnDeriv_withDensity ν hq).symm


-- created on 2020-12-07
