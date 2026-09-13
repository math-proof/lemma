import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/--
A marginal of a joint probability space admitting a density also admits a density: if
`PSpace 𝕡 (x ⊗ y)` holds, then `PSpace 𝕡 x` holds. The a.e. measurability of the pair is
part of the joint `PSpace`, so the first projection is a.e. measurable and its pushforward
step only needs the a.e. version of `map_map`. The marginal density of the first
component is the section integral `q xₒ = ∫⁻ yₒ, p (xₒ, yₒ) ∂ReferenceMeasure.measure`
(Tonelli's theorem), and `𝕡.map x = ReferenceMeasure.measure.withDensity q`.
-/
@[main]
private lemma fst
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace 𝕡 (x ⊗ y)) :
-- imply
  PSpace 𝕡 x := by
-- proof
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  let q : α → ENNReal := fun xₒ ↦ lintegral ν (fun yₒ ↦ p (xₒ, yₒ))
  have hq : Measurable q := hp.lintegral_prod_right'
  have hmap : 𝕡.map x =
      (𝕡.map (x ⊗ y)).map Prod.fst :=
    (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
      hP.aemeasurable).symm
  have hlaw : 𝕡.map x = μ.withDensity q := by
    have hjoint : 𝕡.map (x ⊗ y) = (μ.prod ν).withDensity p := hjoint
    rw [hmap, hjoint]
    have hmarg :
        μ.withDensity (fun xₒ ↦ lintegral ν (fun yₒ ↦ p (xₒ, yₒ))) =
          ((μ.prod ν).withDensity p).fst := by
      ext s hs
      rw [withDensity_apply _ hs]
      have h : ((μ.prod ν).withDensity p).fst s =
          lintegral (μ.restrict s) (fun xₒ ↦ lintegral ν (fun yₒ ↦ p (xₒ, yₒ))) := by
        rw [Measure.fst_apply hs, ← Set.prod_univ,
          withDensity_apply _ (MeasurableSet.prod hs MeasurableSet.univ),
          setLIntegral_prod p (hp.aemeasurable.restrict)]
        simp only [setLIntegral_univ]
      exact h.symm
    exact hmarg.symm
  exact { toIsProbabilityMeasure := inferInstance, aemeasurable := AEMeasurable.fst hP.aemeasurable, exists_distribution := ⟨q, ⟨hq⟩, hlaw⟩ }


/--
A marginal of a joint probability space admitting a density also admits a density: if
`PSpace 𝕡 (x ⊗ y)` holds, then `PSpace 𝕡 y` holds. The a.e. measurability of the pair is
part of the joint `PSpace`, so the second projection is a.e. measurable and its pushforward
step only needs the a.e. version of `map_map`. The marginal density of the second
component is the section integral `q yₒ = ∫⁻ xₒ, p (xₒ, yₒ) ∂ReferenceMeasure.measure`
(Tonelli's theorem), and `𝕡.map y = ReferenceMeasure.measure.withDensity q`.
-/
@[main]
private lemma snd
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace 𝕡 (x ⊗ y)) :
-- imply
  PSpace 𝕡 y := by
-- proof
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  let q : β → ENNReal := fun yₒ ↦ lintegral μ (fun xₒ ↦ p (xₒ, yₒ))
  have hq : Measurable q := hp.lintegral_prod_left'
  have hmap : 𝕡.map y =
      (𝕡.map (x ⊗ y)).map Prod.snd :=
    (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
      hP.aemeasurable).symm
  have hlaw : 𝕡.map y = ν.withDensity q := by
    have hjoint : 𝕡.map (x ⊗ y) = (μ.prod ν).withDensity p := hjoint
    rw [hmap, hjoint]
    have hmarg :
        ν.withDensity (fun yₒ ↦ lintegral μ (fun xₒ ↦ p (xₒ, yₒ))) =
          ((μ.prod ν).withDensity p).snd := by
      ext s hs
      rw [withDensity_apply _ hs]
      have h : ((μ.prod ν).withDensity p).snd s =
          lintegral (ν.restrict s) (fun yₒ ↦ lintegral μ (fun xₒ ↦ p (xₒ, yₒ))) := by
        rw [Measure.snd_apply hs, ← Set.univ_prod,
          withDensity_apply _ (MeasurableSet.prod MeasurableSet.univ hs),
          setLIntegral_prod_symm p (hp.aemeasurable.restrict)]
        simp only [setLIntegral_univ]
      exact h.symm
    exact hmarg.symm
  exact { toIsProbabilityMeasure := inferInstance, aemeasurable := AEMeasurable.snd hP.aemeasurable, exists_distribution := ⟨q, ⟨hq⟩, hlaw⟩ }


-- created on 2026-09-13
