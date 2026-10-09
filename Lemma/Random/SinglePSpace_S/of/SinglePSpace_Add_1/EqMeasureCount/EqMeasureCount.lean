import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import sympy.stats.hidden_markov_sequence
open MeasureTheory Measure Random


/--
With counting reference measures on the (countable, discrete) state and action spaces, a joint density of
`x` with the history `(s, a)[:t + 1]` is a joint density of `x` with the split history
`((s, a)[:t], (s t, a t))`: the bijection `f ↦ (Fin.init f, f (Fin.last t))` carries the counting measure on
`Fin (t + 1) → S × A` to the counting measure on `(Fin t → S × A) × (S × A)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [ReferenceMeasure S] [Countable S] [MeasurableSingletonClass S]
  [ReferenceMeasure A] [Countable A] [MeasurableSingletonClass A]
  {π : Measure Ω}
  {x : Ω → α}
  {s : ℕ → Ω → S}
  {a : ℕ → Ω → A}
  {t : ℕ}
-- given
  (hS : ReferenceMeasure.measure (α := S) = Measure.count)
  (hA : ReferenceMeasure.measure (α := A) = Measure.count)
  (h : SinglePSpace π (x, (s, a)[:t + 1])) :
-- imply
  SinglePSpace π (x, (s, a)[:t], ((s t, a t) : Ω → S × A)) := by
-- proof
  -- the bijection `f ↦ (Fin.init f, f (Fin.last t))` preserves the counting measures
  let e : (Fin (t + 1) → S × A) → (Fin t → S × A) × (S × A) := fun f ↦ (Fin.init f, f (Fin.last t))
  have he : MeasurePreserving e Measure.count
    ((Measure.count : Measure (Fin t → S × A)).prod ((ReferenceMeasure.measure (α := S)).prod ReferenceMeasure.measure)) := by
    refine ⟨measurable_of_countable e, ?_⟩
    rw [hS, hA, ProdCountS.eq.Count, ProdCountS.eq.Count]
    refine Measure.ext_iff_singleton.mpr fun z ↦ ?_
    have hpre : e ⁻¹' {z} = {Fin.snoc (α := fun _ ↦ S × A) z.1 z.2} := by
      ext f
      simp only [Set.mem_preimage, Set.mem_singleton_iff, e]
      constructor
      ·
        rintro rfl
        exact (Fin.snoc_init_self f).symm
      ·
        rintro rfl
        simp [Fin.init_snoc, Fin.snoc_last]
    rw [Measure.map_apply (measurable_of_countable e) (measurableSet_singleton z), hpre, count_singleton, count_singleton]
  have hΦ := (MeasurePreserving.id (ReferenceMeasure.measure (α := α))).prod he
  obtain ⟨ρ, D, hD⟩ := h.exists_distribution
  have hD' : π.map (x, (s, a)[:t + 1]) = ReferenceMeasure.measure.withDensity ρ := hD
  have hY : AEMeasurable (x, (s, a)[:t], ((s t, a t) : Ω → S × A)) π :=
    hΦ.measurable.comp_aemeasurable h.aemeasurable
  have hac : π.map (x, (s, a)[:t], ((s t, a t) : Ω → S × A)) ≪ ReferenceMeasure.measure := by
    have hmap : π.map (x, (s, a)[:t], ((s t, a t) : Ω → S × A)) = (π.map (x, (s, a)[:t + 1])).map (Prod.map id e) :=
      (AEMeasurable.map_map_of_aemeasurable hΦ.measurable.aemeasurable h.aemeasurable).symm
    change _ ≪ (ReferenceMeasure.measure (α := α)).prod
      ((Measure.count : Measure (Fin t → S × A)).prod ((ReferenceMeasure.measure (α := S)).prod ReferenceMeasure.measure))
    rw [hmap, ← hΦ.map_eq, hD']
    exact (withDensity_absolutelyContinuous _ _).map hΦ.measurable
  apply SinglePSpace.of.AEMeasurable.Distributed (D := ⟨Measure.measurable_rnDeriv (π.map (x, (s, a)[:t], ((s t, a t) : Ω → S × A))) ReferenceMeasure.measure⟩)
    _ hY
  exact (withDensity_rnDeriv_eq _ _ hac).symm


-- created on 2026-10-07
