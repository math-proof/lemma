import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
open MeasureTheory


/--
| attributes | lemma |
| :---: | :---: |
| path | Random.SinglePSpace.SinglePSpace.of.SinglePSpace |
| And.left | Random.SinglePSpace.of.SinglePSpace.fst |
| And.right | Random.SinglePSpace.of.SinglePSpace.snd |
-/
@[path, And.left, And.right]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : SinglePSpace π (x, y)) :
-- imply
  SinglePSpace π x ∧ SinglePSpace π y := by
-- proof
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  refine ⟨?_, ?_⟩
  ·
    let q : α → ENNReal := fun «x.bvar» ↦ lintegral ν (fun «y.bvar» ↦ p («x.bvar», «y.bvar»))
    have hq : Measurable q := hp.lintegral_prod_right'
    have hmap : π.map x = (π.map (x, y)).map Prod.fst :=
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
        hP.aemeasurable).symm
    refine {
      toIsProbabilityMeasure := inferInstance
      aemeasurable := AEMeasurable.fst hP.aemeasurable
      exists_distribution := ⟨q, ⟨hq⟩, ?_⟩ }
    change π.map x = μ.withDensity q
    have hjoint' : π.map (x, y) = (μ.prod ν).withDensity p := hjoint
    rw [hmap, hjoint']
    apply Eq.symm
    change μ.withDensity q = ((μ.prod ν).withDensity p).fst
    ext s hs
    rw [withDensity_apply _ hs]
    apply Eq.symm
    rw [Measure.fst_apply hs, ← Set.prod_univ,
      withDensity_apply _ (MeasurableSet.prod hs MeasurableSet.univ),
      setLIntegral_prod p hp.aemeasurable.restrict]
    simp [q]
  ·
    let q : β → ENNReal := fun «y.bvar» ↦ lintegral μ (fun «x.bvar» ↦ p («x.bvar», «y.bvar»))
    have hq : Measurable q := hp.lintegral_prod_left'
    have hmap : π.map y = (π.map (x, y)).map Prod.snd :=
      (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        hP.aemeasurable).symm
    refine {
      toIsProbabilityMeasure := inferInstance
      aemeasurable := AEMeasurable.snd hP.aemeasurable
      exists_distribution := ⟨q, ⟨hq⟩, ?_⟩ }
    change π.map y = ν.withDensity q
    have hjoint' : π.map (x, y) = (μ.prod ν).withDensity p := hjoint
    rw [hmap, hjoint']
    apply Eq.symm
    change ν.withDensity q = ((μ.prod ν).withDensity p).snd
    ext s hs
    rw [withDensity_apply _ hs]
    apply Eq.symm
    rw [Measure.snd_apply hs, ← Set.univ_prod,
      withDensity_apply _ (MeasurableSet.prod MeasurableSet.univ hs),
      setLIntegral_prod_symm p hp.aemeasurable.restrict]
    simp [q]


-- created on 2026-09-14
-- updated on 2026-10-23
