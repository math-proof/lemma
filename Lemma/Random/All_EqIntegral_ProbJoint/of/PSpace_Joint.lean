import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
open Random MeasureTheory


/-- `π.prob (x, y)` is a.e. equal to any witnessing density `p` supplied by
`PSpace.exists_distribution` (the joint law equals `μ.prod ν` with density `p`). -/
private lemma densityAe
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω} {x : Ω → α} {y : Ω → β}
  [PSpace π (x, y)]
-- given
  (p : α × β → ENNReal)
  (hp : Measurable p)
  (hjoint : π.map (x, y) = (ReferenceMeasure.measure.prod ReferenceMeasure.measure).withDensity p) :
-- imply
  π.prob (x, y) =ᵐ[ReferenceMeasure.measure.prod ReferenceMeasure.measure] p := by
-- proof
  show (π.map (x, y)).rnDeriv _ =ᵐ[_] p
  rw [hjoint]
  apply Measure.rnDeriv_withDensity _ hp


@[main, comm]
private lemma left
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω} {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace π (x, y)) :
-- imply
  have := PSpace.of.PSpace_Joint.snd hP
  ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
    ∫⁻ «x.bvar», ℙ[π](x = «x.bvar» ∧ y = «y.bvar») ∂ReferenceMeasure.measure =
      ℙ[π](y = «y.bvar») := by
-- proof
  simp
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  let q := fun «y.bvar» : β ↦ lintegral μ (fun «x.bvar» ↦ p («x.bvar», «y.bvar»))
  have hlaw : π.map y = ν.withDensity q := by
    erw [← AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hP.aemeasurable, hjoint]
    symm
    ext s hs
    rw [withDensity_apply _ hs]
    symm
    change ((μ.prod ν).withDensity p).snd s = _
    rw [Measure.snd_apply hs, ← Set.univ_prod,
      withDensity_apply _ (MeasurableSet.prod MeasurableSet.univ hs),
      setLIntegral_prod_symm p (hp.aemeasurable.restrict)]
    simp only [setLIntegral_univ]
    rfl
  apply Filter.EventuallyEq.trans (g := q)
  · apply (Measure.ae_ae_of_ae_prod
        (ae_eq_comp measurable_swap.aemeasurable
          (_ : π.prob (x, y) =ᵐ[(ν.prod μ).map Prod.swap] p))).mono
    · intro _ hb
      apply lintegral_congr_ae hb
    · simpa [Measure.prod_swap] using densityAe p hp hjoint
  · symm
    change (π.map y).rnDeriv ν =ᵐ[ν] q
    rw [hlaw]
    apply Measure.rnDeriv_withDensity ν hp.lintegral_prod_left'


/--
| attributes | lemma |
| :---: | :---: |
| main | Random.All_EqIntegral_ProbJoint.of.PSpace_Joint |
| comm | Random.All_Eq_Integral_ProbJoint.of.PSpace_Joint |
-/
@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω} {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace π (x, y)) :
-- imply
  have := PSpace.of.PSpace_Joint.fst hP
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure,
    ∫⁻ «y.bvar», ℙ[π](x = «x.bvar» ∧ y = «y.bvar») ∂ReferenceMeasure.measure =
      ℙ[π](x = «x.bvar») := by
-- proof
  simp
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  let q := fun «x.bvar» : α ↦ lintegral ν (fun «y.bvar» ↦ p («x.bvar», «y.bvar»))
  have hlaw : π.map x = μ.withDensity q := by
    erw [← AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hP.aemeasurable, hjoint]
    symm
    ext s hs
    rw [withDensity_apply _ hs]
    symm
    change ((μ.prod ν).withDensity p).fst s = _
    rw [Measure.fst_apply hs, ← Set.prod_univ,
      withDensity_apply _ (MeasurableSet.prod hs MeasurableSet.univ),
      setLIntegral_prod p (hp.aemeasurable.restrict)]
    simp only [setLIntegral_univ]
    rfl
  apply Filter.EventuallyEq.trans (g := q)
  · apply (Measure.ae_ae_of_ae_prod (densityAe p hp hjoint)).mono
    intro _ hb
    apply lintegral_congr_ae hb
  · symm
    change (π.map x).rnDeriv μ =ᵐ[μ] q
    rw [hlaw]
    apply Measure.rnDeriv_withDensity μ hp.lintegral_prod_right'


-- created on 2020-12-07
-- updated on 2026-09-20
