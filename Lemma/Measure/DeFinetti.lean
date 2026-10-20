import Mathlib
import sympy.Basic
import sympy.atlas.Probability.DeFinetti
open MeasureTheory Set
open MathlibExt.Probability.DeFinettiWanted


/--
[deFinetti_binary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/DeFinetti.lean)
-/
@[path]
private lemma deFinetti_binary_eq
  {μ : ProbabilityMeasure (ℕ → Bool)}
-- given
  (hμ : ∀ (σ : Equiv.Perm ℕ), Set.Finite {n : ℕ | σ n ≠ n} → Measure.map (fun ω : ℕ → Bool => ω ∘ ⇑σ) (μ : Measure (ℕ → Bool)) = (μ : Measure (ℕ → Bool))) :
-- imply
  ∃ (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)),
    ∀ (A B : Finset ℕ), Disjoint A B →
    (μ : Measure (ℕ → Bool))
    {ω : ℕ → Bool | (∀ i ∈ A, ω i = true) ∧ (∀ i ∈ B, ω i = false)} =
    ENNReal.ofReal
    (MeasureTheory.integral (ν : Measure (Set.Icc (0 : ℝ) 1))
    (fun p : Set.Icc (0 : ℝ) 1 =>
    (p.val : ℝ) ^ A.card * (1 - (p.val : ℝ)) ^ B.card)) := by
-- proof
  apply MathlibExt.Probability.DeFinettiWanted.deFinetti_binary μ hμ


-- created on 2026-10-20
