module

public import Theorem.Random.Any_And.of.In.IsOpen
public import Theorem.Random.Any_And_Any_And_InToRealMapMeasureAndAll_LtToNNRealIntegral_ENNReal.of.Gt_0
public import Theorem.Random.IsProbabilityMeasure.of.Gt_0
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.MetricSpace.Polish

public section

open Classical MeasureTheory Random
open scoped ENNReal


universe u


/--
An open set of the weak topology contains the empirical measures whose cell masses lie in a small
open set of frequencies. The cells come from one finite measurable map, the reference probability
itself has cell masses in that open set, and the containment holds for every positive sample size.
-/
public theorem Random.Any_And_Any_And_InAndAll_InSMul.of.In.IsOpen
  {α : Type u} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {U : Set (ProbabilityMeasure α)} {ν : ProbabilityMeasure α}
-- given
  (hU : IsOpen U)
  (hν : ν ∈ U) :
-- imply
  ∃ β : Type u, ∃ _ : Fintype β, ∃ _ : MeasurableSpace β, ∃ _ : MeasurableSingletonClass β,
    ∃ φ : α → β, Measurable φ ∧
    ∃ V : Set (β → ℝ), IsOpen V ∧
      (fun a => ((ν : Measure α).map φ {a}).toReal) ∈ V ∧
      ∀ {n : ℕ} (hn : 0 < n) (ω : Fin n → α),
        (fun a => ((((n : ENNReal)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i)).map φ) {a}).toReal) ∈ V →
        (⟨(n : ENNReal)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i),
          IsProbabilityMeasure.of.Gt_0 hn⟩ : ProbabilityMeasure α) ∈ U :=
-- proof
by
  obtain ⟨s, ε, hε, hball⟩ := Any_And.of.In.IsOpen hU hν
  obtain ⟨N, φ, hφ, V, hVopen, hνV, hfiber⟩ :=
    Any_And_Any_And_InToRealMapMeasureAndAll_LtToNNRealIntegral_ENNReal.of.Gt_0 (ν := ν) (s := s) hε
  refine ⟨↥s → Fin (N + 1), inferInstance, inferInstance, inferInstance, φ, hφ, V, hVopen, hνV, ?_⟩
  intro n hn ω hmass
  let ρ : ProbabilityMeasure α :=
    ⟨(n : ENNReal)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i), IsProbabilityMeasure.of.Gt_0 hn⟩
  apply hball ρ
  apply hfiber ρ
  simpa [ρ] using hmass


-- created on 2026-11-02
