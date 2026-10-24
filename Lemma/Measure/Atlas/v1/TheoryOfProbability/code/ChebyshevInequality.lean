import Mathlib
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
[chebyshev_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ChebyshevInequality.lean)
-/
@[path]
lemma chebyshev_inequality
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsFiniteMeasure μ]
  {X : Ω → ℝ}
  {a : ℝ}
-- given
  (hX : MemLp X 2 μ)
  (ha : 0 < a) :
-- imply
  μ.real {ω | a ≤ |X ω - μ[X]|} ≤ Var[X; μ] / a ^ 2 := by
-- proof
  have hY_nn : 0 ≤ᵐ[μ] (fun ω => (X ω - μ[X]) ^ 2) :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hY_int : Integrable (fun ω => (X ω - μ[X]) ^ 2) μ :=
    (hX.sub (memLp_const _)).integrable_sq
  have ha2 : (0 : ℝ) < a ^ 2 := sq_pos_of_pos ha
  have markov := markov_inequality hY_nn hY_int ha2
  have hset : {ω | a ^ 2 ≤ (X ω - μ[X]) ^ 2} = {ω | a ≤ |X ω - μ[X]|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [sq_le_sq, abs_of_pos ha]
  rw [hset] at markov
  have hvar : (∫ ω, (X ω - μ[X]) ^ 2 ∂μ) = Var[X; μ] :=
    (variance_eq_integral hX.1.aemeasurable).symm
  rwa [hvar] at markov


-- created on 2026-10-23
