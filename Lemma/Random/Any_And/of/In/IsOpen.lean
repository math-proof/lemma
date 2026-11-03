import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Initialize.Tactic.Attr.Basic
open Classical MeasureTheory Metric Set Topology


/--
An open set in the topology of weak convergence contains a basic neighborhood of any of its
probabilities. The basic neighborhood fixes finitely many nonnegative bounded continuous test
functions and requires their integrals to stay within a positive distance of the reference values.
-/
@[path]
private lemma main
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {U : Set (ProbabilityMeasure α)} {ν : ProbabilityMeasure α}
-- given
  (hU : IsOpen U)
  (hν : ν ∈ U) :
-- imply
  ∃ s : Finset (BoundedContinuousFunction α NNReal), ∃ ε : ℝ, 0 < ε ∧
    ∀ ρ : ProbabilityMeasure α,
      (∀ f ∈ s, dist
        (lintegral (ρ : Measure α) (fun x => (f x : ENNReal))).toNNReal
        (lintegral (ν : Measure α) (fun x => (f x : ENNReal))).toNNReal < ε) →
        ρ ∈ U :=
-- proof
by
  let _ := TopologicalSpace.upgradeIsCompletelyMetrizable α
  let g : ProbabilityMeasure α → WeakDual NNReal (BoundedContinuousFunction α NNReal) :=
    fun ρ => ρ.toWeakDualBCNN
  have hg : IsEmbedding g :=
    IsEmbedding.comp (FiniteMeasure.isEmbedding_toWeakDualBCNN α)
      (ProbabilityMeasure.toFiniteMeasure_isEmbedding α)
  let c : WeakDual NNReal (BoundedContinuousFunction α NNReal) →
      (BoundedContinuousFunction α NNReal) → NNReal := DFunLike.coe
  have hc : IsEmbedding c := by
    refine WeakBilin.isEmbedding ?_
    intro φ ψ h
    exact ContinuousLinearMap.ext fun x => LinearMap.congr_fun h x
  have he : IsEmbedding (c ∘ g) := IsEmbedding.comp hc hg
  have hmem : U ∈ 𝓝 ν := hU.mem_nhds hν
  rw [he.nhds_eq_comap] at hmem
  obtain ⟨W, hW, hWU⟩ := hmem
  obtain ⟨O, hOW, hO, hνO⟩ := mem_nhds_iff.mp hW
  have hOU : (c ∘ g) ⁻¹' O ⊆ U := (preimage_mono hOW).trans hWU
  obtain ⟨I, u, hu, hbox⟩ := (isOpen_pi_iff.mp hO) (c (g ν)) hνO
  have hball : ∀ f ∈ I, ∃ ε : ℝ, 0 < ε ∧ ball ((c ∘ g) ν f) ε ⊆ u f := by
    intro f hf
    exact Metric.mem_nhds_iff.mp ((hu f hf).1.mem_nhds (hu f hf).2)
  choose εf hεf hsub using hball
  if hne : I.Nonempty then
    let radii : Finset ℝ := I.attach.image (fun p => εf p.1 p.2)
    have hrad : radii.Nonempty := by
      obtain ⟨f, hf⟩ := hne
      exact ⟨εf f hf, Finset.mem_image.mpr ⟨⟨f, hf⟩, Finset.mem_attach _ _, rfl⟩⟩
    have hpos : 0 < radii.min' hrad := by
      rw [Finset.lt_min'_iff]
      intro r hr
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hr
      exact hεf p.1 p.2
    refine ⟨I, radii.min' hrad, hpos, ?_⟩
    intro ρ hρ
    apply hOU
    apply hbox
    intro f hf
    have hle : radii.min' hrad ≤ εf f hf := by
      have hmem : εf f hf ∈ radii :=
        Finset.mem_image.mpr ⟨⟨f, hf⟩, Finset.mem_attach _ _, rfl⟩
      have hleast := radii.isLeast_min' hrad
      simp only [IsLeast, mem_lowerBounds] at hleast
      exact hleast.2 (εf f hf) hmem
    refine hsub f hf (Metric.ball_subset_ball hle (hρ f hf))
  else
    refine ⟨I, 1, one_pos, ?_⟩
    intro ρ hρ
    apply hOU
    apply hbox
    intro f hf
    exact absurd ⟨f, hf⟩ hne


-- created on 2026-11-02
