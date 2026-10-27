import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfProbability.code.MarkovPropertyChain.Part2
open MeasureTheory ProbabilityTheory


/--
[IsMarkovChain.markov_property](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovPropertyChain.lean)
-/
@[path]
lemma IsMarkovChain.markov_property
  {m : MeasurableSpace Ω}
  [MeasurableSpace S]
  {X : ℕ → Ω → S}
  {ℱ : Filtration ℕ m}
  {κ : Kernel S S}
  [IsMarkovKernel κ]
  {μ : Measure Ω}
  {n : ℕ}
  {B : Set S}
-- given
  (hMC : IsMarkovChain X ℱ κ μ)
  (hB : MeasurableSet B) :
-- imply
  μ[(B.indicator (fun _ => (1 : ℝ))) ∘ (X (n + 1)) | ℱ n] =ᵐ[μ] fun ω => (κ (X n ω) B).toReal :=
-- proof
  hMC.markov_prop n B hB

/--
[measurable_shiftPath](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovPropertyChain.lean)
-/
@[path]
lemma measurable_shiftPath
  {m : MeasurableSpace Ω}
  [MeasurableSpace S]
  [MeasurableSpace S]
  {n : ℕ} :
-- imply
  Measurable (shiftPath n : (ℕ → S) → (ℕ → S)) := by
-- proof
  apply measurable_pi_lambda
  intro k
  exact measurable_pi_apply (n + k)

/--
[measurable_markovExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovPropertyChain.lean)
-/
@[path]
lemma measurable_markovExpectation
  {m : MeasurableSpace Ω}
  [MeasurableSpace S]
  {S : Type*}
  [MeasurableSpace S]
  [StandardBorelSpace S]
  [Nonempty S]
  {κ : Kernel S S}
  [IsMarkovKernel κ]
  {Y : (ℕ → S) → ℝ}
-- given
  (hY_meas : @Measurable _ _ MeasurableSpace.pi _ Y)
  (hY_bdd : ∃ C : ℝ, ∀ ω, |Y ω| ≤ C) :
-- imply
  Measurable (markovExpectation S κ Y) := by
-- proof
  let K := ProbabilityTheory.Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0
  let e := MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)
  have hfun : ∀ x : S, markovExpectation S κ Y x = ∫ ω, Y ω ∂(K (e.symm x)) := by
    intro x
    unfold markovExpectation MarkovChainPathMeasure ProbabilityTheory.Kernel.trajMeasure
    congr 1
    rw [Measure.map_dirac' (MeasurableEquiv.measurable _),
      Measure.dirac_bind (Kernel.measurable _)]
  simp_rw [show markovExpectation S κ Y = fun x => ∫ ω, Y ω ∂(K (e.symm x)) from
    funext hfun]
  exact (hY_meas.stronglyMeasurable.integral_kernel).measurable.comp e.symm.measurable

/--
[pathFiltration_le_pi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovPropertyChain.lean)
-/
@[path]
lemma pathFiltration_le_pi
  {m : MeasurableSpace Ω}
  [MeasurableSpace S]
  {S : Type*}
  [MeasurableSpace S]
  {n : ℕ} :
-- imply
  pathFiltration S n ≤ MeasurableSpace.pi := by
-- proof
  exact (pathFiltration S).le' n
/-- Set-integral form of the Markov property for the Markov chain path measure. For any
bounded measurable path functional `Y` and any set `A` measurable with respect to
`pathFiltration S n`,
  `∫_A Y(shiftPath n ω) dP_μ = ∫_A markovExpectation S κ Y (ω n) dP_μ`.
This is the analogue of `setIntegral_shift_eq_pathExpectation` for discrete-time Markov
chains. -/


-- created on 2026-10-23
