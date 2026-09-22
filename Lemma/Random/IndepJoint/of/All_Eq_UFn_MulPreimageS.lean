import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import sympy.stats.joint_rv
import sympy.Basic
open ProbabilityTheory MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (mx : Measurable x) (my : Measurable y) (mz : Measurable z)
  (hrect : ∀ (A : Set α) (B : Set β) (V : Set γ),
      MeasurableSet A → MeasurableSet B → MeasurableSet V →
      π ((x, y) ⁻¹' (A ×ˢ B) ∩ z ⁻¹' V) = π ((x, y) ⁻¹' (A ×ˢ B)) * π (z ⁻¹' V)) :
-- imply
  (x, y) ⟂ᵢ[π] z := by
-- proof
  have mxy : Measurable (x, y) := mx.prodMk my
  rw [IndepFun_iff]
  intro s t hs ht
  obtain ⟨U, hU, rfl⟩ := hs
  obtain ⟨V, hV, rfl⟩ := ht
  have hVΩ : MeasurableSet (z ⁻¹' V) := mz hV
  induction U, hU using MeasurableSpace.induction_on_inter
      (generateFrom_prod (α := α) (β := β)).symm (isPiSystem_prod (α := α) (β := β)) with
  | empty =>
    simp
  | basic W hW =>
    obtain ⟨A, hA, B, hB, rfl⟩ := hW
    exact hrect A B V hA hB hV
  | compl W hW ih =>
    have hWΩ : MeasurableSet ((x, y) ⁻¹' W) := mxy hW
    have hdiff :
        (x, y) ⁻¹' Wᶜ ∩ z ⁻¹' V =
          z ⁻¹' V \ ((x, y) ⁻¹' W ∩ z ⁻¹' V) := by
      ext; simp [and_comm]
    rw [hdiff, measure_sdiff (fun _ h => h.2)
        (hWΩ.inter hVΩ).nullMeasurableSet (measure_ne_top _ _), ih]
    change _ = π (((x, y) ⁻¹' W)ᶜ) * π (z ⁻¹' V)
    rw [measure_compl hWΩ (measure_ne_top _ _), measure_univ,
      mul_comm (1 - _), ENNReal.mul_sub (fun _ _ => measure_ne_top π _), mul_one,
      mul_comm (π ((x, y) ⁻¹' W))]
  | iUnion f hfd hfm ih =>
    have hfmΩ : ∀ i, MeasurableSet ((x, y) ⁻¹' f i) := fun i => mxy (hfm i)
    have hpre_iUnion :
        (x, y) ⁻¹' (⋃ i, f i) = ⋃ i, (x, y) ⁻¹' f i := by
      ext; simp
    rw [hpre_iUnion, Set.iUnion_inter]
    have hdisj :
        Pairwise (Function.onFun Disjoint fun i =>
          (x, y) ⁻¹' f i ∩ z ⁻¹' V) :=
      hfd.mono fun _ _ hij =>
        ((hij.preimage (x, y)).inter_left _).inter_right _
    rw [measure_iUnion hdisj (fun i => (hfmΩ i).inter hVΩ)]
    have hdisj' :
        Pairwise (Function.onFun Disjoint fun i => (x, y) ⁻¹' f i) :=
      hfd.mono fun _ _ hij => hij.preimage _
    rw [measure_iUnion hdisj' hfmΩ, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun i => ih i


-- created on 2026-09-22
