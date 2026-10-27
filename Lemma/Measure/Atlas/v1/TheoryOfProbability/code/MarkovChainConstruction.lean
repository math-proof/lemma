import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.TheoryOfProbability.code.MarkovChainConstruction.Part2
open MeasureTheory ProbabilityTheory Kernel Set


/--
[markovChainMeasure_initial_distribution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainConstruction.lean)
-/
@[path]
lemma markovChainMeasure_initial_distribution
  [MeasurableSpace S]
  {κ : Kernel S S}
  [IsMarkovKernel κ]
  {μ : Measure S}
  [IsProbabilityMeasure μ] :
-- imply
  Measure.map (fun (ω : ℕ → S) => ω 0) (markovChainMeasure κ μ) = μ := by
-- proof
  unfold markovChainMeasure trajMeasure
  rw [Measure.map_comp _ _ (measurable_pi_apply 0)]
  have h_decomp : (fun (f : ℕ → S) => f 0) =
    (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic (0 : ℕ)) => S)) ∘
    (Preorder.frestrictLe 0) := by ext ω; rfl
  rw [h_decomp, Kernel.map_comp_right _ (Preorder.measurable_frestrictLe 0)
    (MeasurableEquiv.piUnique _).measurable]
  rw [traj_map_frestrictLe, partialTraj_self]
  rw [← Measure.map_comp _ _ (MeasurableEquiv.piUnique _).measurable]
  rw [Measure.id_comp]
  rw [Measure.map_map (MeasurableEquiv.piUnique _).measurable
    (MeasurableEquiv.piUnique _).symm.measurable]
  have h_id : ⇑(MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic (0 : ℕ)) => S)) ∘
    ⇑(MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic (0 : ℕ)) => S)).symm = id := by
    ext x; simp [MeasurableEquiv.piUnique]
  rw [h_id, Measure.map_id]

/--
[markovChainMeasure_condDistrib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainConstruction.lean)
-/
@[path]
lemma markovChainMeasure_condDistrib
  [MeasurableSpace S]
  {κ : Kernel S S}
  [IsMarkovKernel κ]
  {μ : Measure S}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  [StandardBorelSpace S]
  [Nonempty S] :
-- imply
  condDistrib (fun (x : ℕ → S) => x (n + 1)) (Preorder.frestrictLe n) (markovChainMeasure κ μ) =ᵐ[Measure.map (Preorder.frestrictLe n) (markovChainMeasure κ μ)] markovLiftKernel κ n := by
-- proof
  exact Kernel.condDistrib_trajMeasure
section ExistenceTheorem

/--
[markov_chain_construction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovChainConstruction.lean)
-/
@[path]
lemma markov_chain_construction
  [MeasurableSpace S]
  {κ : Kernel S S}
  [IsMarkovKernel κ]
  {μ : Measure S}
  [IsProbabilityMeasure μ]
  [StandardBorelSpace S]
  [Nonempty S] :
-- imply
  ∃ (P : Measure (ℕ → S)) (_ : IsProbabilityMeasure P), P.map (fun (ω : ℕ → S) => ω 0) = μ ∧ ∀ n : ℕ, condDistrib (fun (x : ℕ → S) => x (n + 1)) (Preorder.frestrictLe n) P =ᵐ[Measure.map (Preorder.frestrictLe n) P] markovLiftKernel κ n :=
-- proof
  ⟨markovChainMeasure κ μ, markovChainMeasure.isProbabilityMeasure κ μ,
    markovChainMeasure_initial_distribution κ μ,
    fun n => markovChainMeasure_condDistrib κ μ n⟩
end ExistenceTheorem


-- created on 2026-10-23
