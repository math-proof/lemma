import Lemma.Random.PSpace_JointJoint.is.PSpace_Joint_Joint
import Lemma.Random.SinglePSpace.SinglePSpace.of.SinglePSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Prod
import Syntax.Probability.Probability
import Notation.Fun
open MeasureTheory ProbabilityTheory Random Fun


/--
Appending a constant dummy coordinate to the conditioner does not change a
conditional random-argument density, almost surely.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {X : Ω → α} {Y : Ω → β}
  {Z : Ω → Fin 0 → 𝒮}
-- given
  (hXYZ : SinglePSpace π (X, Y, Z)) :
-- imply
  have : SinglePSpace π (X, Y) :=
    SinglePSpace.of.SinglePSpace.fst
      (PSpace_JointJoint.of.PSpace_Joint_Joint hXYZ)
  ℙ[π](X | Y, Z) =ᵐ[π] ℙ[π](X | Y) := by
-- proof
  intro hXY
  have hY : SinglePSpace π Y := SinglePSpace.of.SinglePSpace.snd hXY
  let u0 : Fin 0 → 𝒮 := Fin.elim0
  have hZω (ω : Ω) : Z ω = u0 := by
    funext i
    exact Fin.elim0 i
  have hμ0 :
    ReferenceMeasure.measure (α := Fin 0 → 𝒮) = Measure.dirac u0 := by
    change Measure.pi (fun _ : Fin 0 => ReferenceMeasure.measure (α := 𝒮)) =
      Measure.dirac u0
    exact Measure.pi_of_empty _ u0
  have hrefY :
    ReferenceMeasure.measure (α := β × (Fin 0 → 𝒮)) =
      (ReferenceMeasure.measure (α := β)).map (fun y => (y, u0)) := by
    change
      (ReferenceMeasure.measure (α := β)).prod
        (ReferenceMeasure.measure (α := Fin 0 → 𝒮)) = _
    rw [hμ0, Measure.prod_dirac]
  have href :
    ReferenceMeasure.measure (α := α × (β × (Fin 0 → 𝒮))) =
      (ReferenceMeasure.measure (α := α × β)).map
        (Prod.map (id : α → α) (fun y : β => (y, u0))) := by
    change
      (ReferenceMeasure.measure (α := α)).prod
        ((ReferenceMeasure.measure (α := β)).prod
          (ReferenceMeasure.measure (α := Fin 0 → 𝒮))) = _
    rw [hμ0, Measure.prod_dirac]
    have hμprod :
      ReferenceMeasure.measure (α := α × β) =
        (ReferenceMeasure.measure (α := α)).prod
          (ReferenceMeasure.measure (α := β)) :=
      rfl
    rw [hμprod]
    simpa [Measure.map_id] using
      (Measure.map_prod_map
        (ReferenceMeasure.measure (α := α))
        (ReferenceMeasure.measure (α := β))
        measurable_id measurable_prodMk_right)
  have hfembY : MeasurableEmbedding (fun y : β => (y, u0)) := by
    refine ⟨fun _ _ h => congrArg Prod.fst h, measurable_prodMk_right, ?_⟩
    intro s hs
    have himg :
      (fun y : β => (y, u0)) '' s =
        s ×ˢ (Set.univ : Set (Fin 0 → 𝒮)) := by
      ext ⟨y, z⟩
      have hz : z = u0 := Subsingleton.elim z u0
      simp [Set.mem_prod, hz]
    rw [himg]
    exact hs.prod MeasurableSet.univ
  have hfemb :
    MeasurableEmbedding
      (Prod.map (id : α → α) (fun y : β => (y, u0))) :=
    MeasurableEmbedding.id.prodMap hfembY
  let e := (X, Y, Z)
  let f := (X, Y)
  let eYZ := (Y, Z)
  have hfun :
    (e : Ω → α × (β × (Fin 0 → 𝒮))) =
      Prod.map (id : α → α) (fun y : β => (y, u0)) ∘ (f : Ω → α × β) := by
    funext ω
    apply Prod.ext
    · rfl
    · exact Prod.ext rfl (hZω ω)
  have hfunY :
    (eYZ : Ω → β × (Fin 0 → 𝒮)) = (fun y => (y, u0)) ∘ Y := by
    funext ω
    exact Prod.ext rfl (hZω ω)
  have hmap :
    π.map e =
      (π.map f).map (Prod.map (id : α → α) (fun y : β => (y, u0))) := by
    rw [hfun]
    exact (AEMeasurable.map_map_of_aemeasurable
      hfemb.measurable.aemeasurable hXY.aemeasurable).symm
  have hmapY : π.map eYZ = (π.map Y).map (fun y => (y, u0)) := by
    rw [hfunY]
    exact (AEMeasurable.map_map_of_aemeasurable
      measurable_prodMk_right.aemeasurable hY.aemeasurable).symm
  have habsXY : π.map f ≪ ReferenceMeasure.measure (α := α × β) := by
    obtain ⟨ρ, _, hlaw⟩ := hXY.exists_distribution
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have habsY : π.map Y ≪ ReferenceMeasure.measure (α := β) := by
    obtain ⟨ρ, _, hlaw⟩ := hY.exists_distribution
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have hrd :=
    hfemb.rnDeriv_map (π.map f) (ReferenceMeasure.measure (α := α × β))
  have hrdY :=
    hfembY.rnDeriv_map (π.map Y) (ReferenceMeasure.measure (α := β))
  have hnum :
    (fun ω => (π.map e).rnDeriv ReferenceMeasure.measure (e ω)) =ᵐ[π]
      fun ω => (π.map f).rnDeriv ReferenceMeasure.measure (f ω) := by
    have hrd' :
      (fun p =>
        (π.map e).rnDeriv ReferenceMeasure.measure
          (Prod.map (id : α → α) (fun y : β => (y, u0)) p)) =ᵐ[ReferenceMeasure.measure (α := α × β)]
      fun p => (π.map f).rnDeriv ReferenceMeasure.measure p := by
      simpa [hmap, href] using hrd
    have h1 := ae_of_ae_map hXY.aemeasurable (habsXY.ae_le hrd')
    filter_upwards [h1] with ω h
    rwa [congr_fun hfun ω]
  have hden :
    (fun ω => (π.map eYZ).rnDeriv ReferenceMeasure.measure (eYZ ω)) =ᵐ[π]
      fun ω => (π.map Y).rnDeriv ReferenceMeasure.measure (Y ω) := by
    have hrd' :
      (fun y => (π.map eYZ).rnDeriv ReferenceMeasure.measure (y, u0)) =ᵐ[ReferenceMeasure.measure (α := β)]
      fun y => (π.map Y).rnDeriv ReferenceMeasure.measure y := by
      simpa [hmapY, hrefY] using hrdY
    have h1 := ae_of_ae_map hY.aemeasurable (habsY.ae_le hrd')
    filter_upwards [h1] with ω h
    rwa [congr_fun hfunY ω]
  filter_upwards [hnum, hden] with ω hn hd
  change π.condProb e (e ω) = π.condProb f (f ω)
  simp [Measure.condProb, Measure.prob]
  have hsnd_e : (fun ω' => (e ω').2) = eYZ := rfl
  have hsnd_f : (fun ω' => (f ω').2) = Y := rfl
  have hval_e : (e ω).2 = eYZ ω := rfl
  have hval_f : (f ω).2 = Y ω := rfl
  rw [hsnd_e, hsnd_f, hval_e, hval_f, hn, hd]


-- created on 2026-11-19
