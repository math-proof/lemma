import Structure.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient


/--
The initial state distribution of a stochastic MDP is a probability measure:
its real mass on `Set.univ` is `1`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSpace 𝒜]
  {M : StochasticMDP 𝒮 𝒜} :
-- imply
  ((M.init : ProbabilityMeasure 𝒮) : Measure 𝒮).real Set.univ = 1 :=
-- proof
  probReal_univ


-- created on 2026-10-06
-- updated on 2026-11-18
