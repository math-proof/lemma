import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.symbolic_probability
import sympy.Basic
open MeasureTheory


private lemma marginal
  {α β : Type*}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}
  [SFinite μ] [SFinite ν]
-- given
  (p : α × β → ENNReal)
  (hp : Measurable p) :
-- imply
  ν.withDensity (fun y ↦ lintegral μ (fun x ↦ p (x, y))) = ((μ.prod ν).withDensity p).snd := by
-- proof
  ext s hs
  rw [withDensity_apply _ hs]
  have h : ((μ.prod ν).withDensity p).snd s =
      lintegral (ν.restrict s) (fun y ↦ lintegral μ (fun x ↦ p (x, y))) := by
    rw [Measure.snd_apply hs, ← Set.univ_prod,
      withDensity_apply _ (MeasurableSet.prod MeasurableSet.univ hs),
      setLIntegral_prod_symm p (hp.aemeasurable.restrict)]
    simp only [setLIntegral_univ]
  exact h.symm


/--
Marginal density of `y`: integrating out `x` from the joint density `Pr(x, y)`
yields the density of `y` (evaluated along the random variable `y`), a.e.\[`ℙ`].

Latex rendering presents this as `∫ 𝕡(x, y) dx = 𝕡(y)` (sympy-style).
-/
@[main]
private lemma main
  [MeasurableSpace (Ω : Type*)]
  [ReferenceMeasure (α : Type*)]
  [ReferenceMeasure (β : Type*)]
  {ℙ : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : Probability x y ℙ)
  (hx : Measurable x)
  (hy : Measurable y) :
-- imply
  (fun ω ↦ lintegral (Probability.measure α) (fun a ↦ Probability.density x y ℙ (a, y ω))) =ᵐ[ℙ]
    (fun ω ↦ ((Measure.map y ℙ).rnDeriv (Probability.measure β)) (y ω)) := by
-- proof
  obtain ⟨p, hp, hjoint⟩ := hP.exists_density
  let μ := Probability.measure α
  let ν := Probability.measure β
  let q := fun b : β ↦ lintegral μ (fun a ↦ p (a, b))
  have hq : Measurable q := hp.lintegral_prod_left'
  have hmap : Measure.map y ℙ =
      Measure.map Prod.snd (Measure.map (fun ω ↦ (x ω, y ω)) ℙ) :=
    (Measure.map_map measurable_snd
      (by fun_prop : Measurable (fun ω ↦ (x ω, y ω)))).symm
  have hlaw : Measure.map y ℙ = ν.withDensity q := by
    rw [hmap, hjoint]
    exact (marginal p hp).symm
  have hjp : Probability.density x y ℙ =ᵐ[μ.prod ν] p := by
    change (Measure.map (fun ω ↦ (x ω, y ω)) ℙ).rnDeriv (μ.prod ν) =ᵐ[μ.prod ν] p
    rw [hjoint]
    exact Measure.rnDeriv_withDensity (μ.prod ν) hp
  have hsec : (fun b ↦ lintegral μ (fun a ↦ Probability.density x y ℙ (a, b))) =ᵐ[ν] q := by
    have hjp' : Probability.density x y ℙ =ᵐ[(ν.prod μ).map Prod.swap] p := by
      rwa [Measure.prod_swap]
    have hswap :
        (fun z : β × α ↦ Probability.density x y ℙ (z.2, z.1)) =ᵐ[ν.prod μ]
          fun z ↦ p (z.2, z.1) :=
      ae_eq_comp measurable_swap.aemeasurable hjp'
    exact (Measure.ae_ae_of_ae_prod hswap).mono fun _ hb ↦ lintegral_congr_ae hb
  have hold : (fun ω ↦ q (y ω)) =ᵐ[ℙ]
      (fun ω ↦ ((Measure.map y ℙ).rnDeriv ν) (y ω)) := by
    rw [hlaw]
    exact ae_eq_comp' hy.aemeasurable (Measure.rnDeriv_withDensity ν hq).symm
      (by rw [hlaw]; exact withDensity_absolutelyContinuous _ _)
  have hLHS : (fun ω ↦ lintegral μ (fun a ↦ Probability.density x y ℙ (a, y ω))) =ᵐ[ℙ]
      (fun ω ↦ q (y ω)) :=
    ae_eq_comp' hy.aemeasurable hsec
      (by rw [hlaw]; exact withDensity_absolutelyContinuous _ _)
  exact hLHS.trans hold


-- created on 2020-12-07
-- updated on 2026-09-11
