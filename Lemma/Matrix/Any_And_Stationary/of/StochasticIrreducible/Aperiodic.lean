import sympy.stats.stochastic_process_types
import sympy.stats.stochastic_process
import Lemma.Matrix.Any_And_DoeblinMinorizationPow.is.Nonempty.Aperiodic
import Lemma.Matrix.Any_And_ContractingWith.of.DoeblinMinorization
import Lemma.Matrix.Any_And_Stationary.of.RowStochastic
import Lemma.Matrix.Stationary_Pow.of.Stationary
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (h₀ : Aperiodic P)
  (h₁ : StochasticIrreducible P) :
-- imply
  ∃! μ : S → ℝ, StochasticVec μ ∧ Stationary μ P := by
-- proof
  obtain ⟨μ, hμ, hμP⟩ := Any_And_Stationary.of.RowStochastic (P := P)
  obtain ⟨N, -, hN⟩ := Any_And_DoeblinMinorizationPow.of.Nonempty.Aperiodic (P := P) inferInstance h₀
  obtain ⟨K, -, hf⟩ := Any_And_ContractingWith.of.DoeblinMinorization hN
  have hfix : ∀ x (hx : StochasticVec x), Stationary x P → Function.IsFixedPt (smat_as_operator (P ^ N)) ⟨ofL1 x, by simpa [ofL1] using hx⟩ := by
    intro x hx hxP
    apply Subtype.ext
    simp [smat_as_operator, ofL1]
    apply (Stationary_Pow.of.Stationary hxP (n := N)).stationary
  apply ExistsUnique.intro μ ⟨hμ, hμP⟩
  intro ν ⟨hν, hνP⟩
  simpa [ofL1] using congrArg (fun z : Simplex S => WithLp.ofLp (z : l1Space S)) ((hf.fixedPoint_unique (hfix ν hν hνP)).trans (hf.fixedPoint_unique (hfix μ hμ hμP)).symm)


-- created on 2026-09-22
-- updated on 2026-09-26
