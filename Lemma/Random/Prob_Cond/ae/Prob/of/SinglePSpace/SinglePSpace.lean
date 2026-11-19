import Lemma.Random.SinglePSpace.SinglePSpace.of.SinglePSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Prod
import Syntax.Probability.Probability
import Notation.Fun
open MeasureTheory ProbabilityTheory Random Fun


/--
Conditioning a random variable on a constant dummy coordinate in `Fin 0 → 𝒮`
does not change its random-argument density, almost surely.
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
  (hX : SinglePSpace π X)
  (hXZ : SinglePSpace π (X, Z)) :
-- imply
  have : Z = fun _ => Fin.elim0 := by
    funext ω i
    exact Fin.elim0 i
  ℙ[π](X | Z) =ᵐ[π] ℙ[π](X) := by
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
  let e := (X, Z)
  have hfun : (e : Ω → α × (Fin 0 → 𝒮)) = (fun a => (a, u0)) ∘ X := by
    funext ω
    exact Prod.ext rfl (hZω ω)
  have hmap : π.map e = (π.map X).map (fun a => (a, u0)) := by
    rw [hfun]
    exact (AEMeasurable.map_map_of_aemeasurable
      measurable_prodMk_right.aemeasurable hX.aemeasurable).symm
  have hfemb : MeasurableEmbedding (fun a : α => (a, u0)) := by
    refine
      ⟨fun _ _ h => congrArg Prod.fst h, measurable_prodMk_right, ?_⟩
    intro s hs
    have himg :
      (fun a : α => (a, u0)) '' s =
        s ×ˢ (Set.univ : Set (Fin 0 → 𝒮)) := by
      ext ⟨a, z⟩
      have hz : z = u0 := Subsingleton.elim z u0
      simp [Set.mem_prod, hz]
    rw [himg]
    exact hs.prod MeasurableSet.univ
  have habsX : π.map X ≪ ReferenceMeasure.measure (α := α) := by
    obtain ⟨ρ, _, hlaw⟩ := hX.exists_distribution
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have hrd :=
    hfemb.rnDeriv_map (π.map X) (ReferenceMeasure.measure (α := α))
  have hrd' :
    (fun a => (π.map e).rnDeriv ReferenceMeasure.measure (a, u0)) =ᵐ[ReferenceMeasure.measure (α := α)]
    fun a => (π.map X).rnDeriv ReferenceMeasure.measure a := by
    simpa [hmap, href] using hrd
  have hnum :
    (fun ω => (π.map e).rnDeriv ReferenceMeasure.measure (e ω)) =ᵐ[π]
      fun ω => (π.map X).rnDeriv ReferenceMeasure.measure (X ω) := by
    have h1 := ae_of_ae_map hX.aemeasurable (habsX.ae_le hrd')
    filter_upwards [h1] with ω h
    rwa [congr_fun hfun ω]
  have hZmap : π.map Z = Measure.dirac u0 := by
    rw [hZ, Measure.map_const, measure_univ, one_smul]
  have habsZ : π.map Z ≪ ReferenceMeasure.measure (α := Fin 0 → 𝒮) := by
    rw [hZmap, hμ0]
  have hden :
    (fun ω => (π.map Z).rnDeriv ReferenceMeasure.measure (Z ω)) =ᵐ[π]
      fun _ => 1 := by
    have hself :
      (fun z => (π.map Z).rnDeriv ReferenceMeasure.measure z) =ᵐ[ReferenceMeasure.measure (α := Fin 0 → 𝒮)] 1 := by
      rw [hZmap, hμ0]
      exact Measure.rnDeriv_self _
    exact ae_of_ae_map (hZ ▸ measurable_const.aemeasurable) (habsZ.ae_le hself)
  filter_upwards [hnum, hden] with ω h hd
  change π.condProb e (e ω) = π.prob X (X ω)
  simp [Measure.condProb, Measure.prob]
  have hsnd : (fun ω' => (e ω').2) = Z := rfl
  have hval : (e ω).2 = Z ω := rfl
  rw [hsnd, hval, hd, h, div_eq_mul_inv, inv_one, mul_one]


-- created on 2026-11-19
