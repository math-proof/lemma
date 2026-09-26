import sympy.stats.markov_samples
import sympy.Basic
import Lemma.Skeleton.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.Real.Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.Iterates.Any_Ge_0AndAll_LeNorm.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.IteratesOfResidual
open Iterates Real


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {sk : Skeleton S d}
-- given
  (k : ℕ) :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ ω y, ‖sk.G (sk.x k ω) y‖ ≤ C := by
-- proof
  obtain ⟨C₁, hC₁, h₁⟩ := Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub (Skeleton.Any_Ge_0AndAll_All_LeNormSub_MulNormSub (sk := sk))
  obtain ⟨C₂, hC₂, h₂⟩ := Any_Ge_0AndAll_LeNorm.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.IteratesOfResidual sk.hx sk.hFlip k
  exact ⟨C₁ * (C₂ + 1), by positivity, fun ω y => (h₁ _ _).trans (by gcongr; exact h₂ ω)⟩


-- created on 2026-09-26