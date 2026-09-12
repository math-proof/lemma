import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/-- `JointPSpace.density` is a.e. equal to any witnessing density `p` supplied by
`JointPSpace.exists_distribution` (the joint law equals `μ.prod ν` with density `p`). -/
private lemma densityAe
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    {𝕡 : Measure Ω}
    {x : Ω → α} {y : Ω → β}
    [JointPSpace 𝕡 x y]
    (p : α × β → ENNReal)
    (hp : Measurable p)
    (hjoint : 𝕡.map (fun ω ↦ (x ω, y ω)) =
      (ReferenceMeasure.measure.prod ReferenceMeasure.measure).withDensity p) :
    JointPSpace.density 𝕡 x y =ᵐ[ReferenceMeasure.measure.prod ReferenceMeasure.measure] p := by
  show (𝕡.map (fun ω ↦ (x ω, y ω))).rnDeriv _ =ᵐ[_] p
  rw [hjoint]
  exact Measure.rnDeriv_withDensity _ hp


@[main]
private lemma left
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : JointPSpace 𝕡 x y)
  (hx : Measurable x)
  (hy : Measurable y) :
-- imply
  (fun b ↦ lintegral ReferenceMeasure.measure (fun a ↦ JointPSpace.density 𝕡 x y (a, b))) =ᵐ[ReferenceMeasure.measure]
    (𝕡.map y).rnDeriv ReferenceMeasure.measure := by
-- proof
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  have hjoint : 𝕡.map (fun ω ↦ (x ω, y ω)) = (μ.prod ν).withDensity p := hjoint
  let q := fun b : β ↦ lintegral μ (fun a ↦ p (a, b))
  have hq : Measurable q := hp.lintegral_prod_left'
  have hlaw : 𝕡.map y = ν.withDensity q := by
    erw [← Measure.map_map measurable_snd (by fun_prop : Measurable (fun ω ↦ (x ω, y ω))), hjoint]
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
  have hjp := densityAe p hp hjoint
  have hsec : (fun b ↦ lintegral μ (fun a ↦ JointPSpace.density 𝕡 x y (a, b))) =ᵐ[ν] q := by
    have hjp' : JointPSpace.density 𝕡 x y =ᵐ[(ν.prod μ).map Prod.swap] p := by
      rwa [Measure.prod_swap]
    have hswap :
        (fun z : β × α ↦ JointPSpace.density 𝕡 x y (z.2, z.1)) =ᵐ[ν.prod μ]
          fun z ↦ p (z.2, z.1) :=
      ae_eq_comp measurable_swap.aemeasurable hjp'
    exact (Measure.ae_ae_of_ae_prod hswap).mono fun _ hb ↦ lintegral_congr_ae hb
  have hrn : (𝕡.map y).rnDeriv ν =ᵐ[ν] q := by
    rw [hlaw]
    exact Measure.rnDeriv_withDensity ν hq
  exact hsec.trans hrn.symm


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : JointPSpace 𝕡 x y)
  (hx : Measurable x)
  (hy : Measurable y) :
-- imply
  (fun a ↦ lintegral ReferenceMeasure.measure (fun b ↦ JointPSpace.density 𝕡 x y (a, b))) =ᵐ[ReferenceMeasure.measure]
    (𝕡.map x).rnDeriv ReferenceMeasure.measure := by
-- proof
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  have hjoint : 𝕡.map (fun ω ↦ (x ω, y ω)) = (μ.prod ν).withDensity p := hjoint
  let q := fun a : α ↦ lintegral ν (fun b ↦ p (a, b))
  have hq : Measurable q := hp.lintegral_prod_right'
  have hlaw : 𝕡.map x = μ.withDensity q := by
    erw [← Measure.map_map measurable_fst (by fun_prop : Measurable (fun ω ↦ (x ω, y ω))), hjoint]
    have hmarg : μ.withDensity (fun x ↦ lintegral ν (fun y ↦ p (x, y))) =
        ((μ.prod ν).withDensity p).fst := by
      ext s hs
      rw [withDensity_apply _ hs]
      have h : ((μ.prod ν).withDensity p).fst s =
          lintegral (μ.restrict s) (fun x ↦ lintegral ν (fun y ↦ p (x, y))) := by
        rw [Measure.fst_apply hs, ← Set.prod_univ,
          withDensity_apply _ (MeasurableSet.prod hs MeasurableSet.univ),
          setLIntegral_prod p (hp.aemeasurable.restrict)]
        simp only [setLIntegral_univ]
      exact h.symm
    exact hmarg.symm
  have hjp := densityAe p hp hjoint
  have hsec : (fun a ↦ lintegral ν (fun b ↦ JointPSpace.density 𝕡 x y (a, b))) =ᵐ[μ] q :=
    (Measure.ae_ae_of_ae_prod hjp).mono fun _ hb ↦ lintegral_congr_ae hb
  have hrn : (𝕡.map x).rnDeriv μ =ᵐ[μ] q := by
    rw [hlaw]
    exact Measure.rnDeriv_withDensity μ hq
  exact hsec.trans hrn.symm


-- created on 2020-12-07
-- updated on 2026-09-12
