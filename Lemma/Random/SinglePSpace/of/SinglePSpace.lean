import Lemma.Random.SinglePSpace.SinglePSpace.of.SinglePSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Prod
import Syntax.Probability.Probability
import Notation.Fun
open MeasureTheory ProbabilityTheory Random Fun


/--
Lift a `SinglePSpace` hypothesis along a constant dummy coordinate in
`Fin 0 → 𝒮`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  [ReferenceMeasure α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {X : Ω → α}
  {Z : Ω → Fin 0 → 𝒮}
-- given
  (hX : SinglePSpace π X) :
-- imply
  have : Z = fun _ => Fin.elim0 := by
    funext ω i
    exact Fin.elim0 i
  SinglePSpace π (X, Z) := by
-- proof
  intro hZ
  let u0 : Fin 0 → 𝒮 := Fin.elim0
  have hZω (ω : Ω) : Z ω = u0 := by rw [hZ]
  have hμ0 :
    ReferenceMeasure.measure (α := Fin 0 → 𝒮) = Measure.dirac u0 := by
    change Measure.pi (fun _ : Fin 0 => ReferenceMeasure.measure (α := 𝒮)) =
      Measure.dirac u0
    exact Measure.pi_of_empty _ u0
  have href :
    ReferenceMeasure.measure (α := α × (Fin 0 → 𝒮)) =
      (ReferenceMeasure.measure (α := α)).map (fun a => (a, u0)) := by
    change
      (ReferenceMeasure.measure (α := α)).prod
        (ReferenceMeasure.measure (α := Fin 0 → 𝒮)) = _
    rw [hμ0, Measure.prod_dirac]
  have hfun : (fun ω => (X ω, Z ω)) = (fun a => (a, u0)) ∘ X := by
    funext ω
    exact Prod.ext rfl (hZω ω)
  have hX_ae : AEMeasurable X π := hX.aemeasurable
  have hpair_ae : AEMeasurable (fun ω => (X ω, Z ω)) π := by
    rw [hfun]
    exact measurable_prodMk_right.comp_aemeasurable hX_ae
  obtain ⟨ρ, hρm, hlaw⟩ := hX.exists_distribution
  let ρ' : α × (Fin 0 → 𝒮) → ENNReal := fun p => ρ p.1
  have hρ'm : Measurable ρ' := hρm.comp measurable_fst
  have hmap :
    π.map (fun ω => (X ω, Z ω)) = (π.map X).map (fun a => (a, u0)) := by
    rw [hfun]
    exact (AEMeasurable.map_map_of_aemeasurable
      measurable_prodMk_right.aemeasurable hX_ae).symm
  have hwd :
    ((ReferenceMeasure.measure (α := α)).withDensity ρ).map (fun a => (a, u0)) =
      ((ReferenceMeasure.measure (α := α)).map (fun a => (a, u0))).withDensity
        ρ' := by
    ext s hs
    rw [Measure.map_apply measurable_prodMk_right hs,
      withDensity_apply _ (measurable_prodMk_right hs),
      withDensity_apply _ hs,
      setLIntegral_map hs hρ'm measurable_prodMk_right]
  refine {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := ?_
    exists_distribution := ⟨ρ', hρ'm, ?_⟩
  }
  ·
    have heq :
      JointRandomSymbol (X, Z).1 (X, Z).2 = fun ω => (X ω, Z ω) := by
      funext ω
      apply Prod.ext
      · rfl
      · rfl
    rwa [heq]
  ·
    change π.map (X, Z) = ReferenceMeasure.measure.withDensity ρ'
    have hmap' : π.map (X, Z) = π.map (fun ω => (X ω, Z ω)) := rfl
    rw [hmap', hmap, hlaw, hwd, href]


-- created on 2026-11-19
