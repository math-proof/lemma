import Mathlib
import Class.Analysis.Misc.Probability.Part2
/-! Some finite probability theory -/


namespace ProbabilityTheory

namespace FinitelyAdditive

variable {A:Type*} [BooleanAlgebra A] (P: FinitelyAdditive A)
         {A':Type*} [BooleanAlgebra A'] (P': FinitelyAdditive A')

@[implicit_reducible] def ExampleProb.map {Ω: ExampleProb P} {f: BoundedLatticeHom A A'} (hf: f.preserves P P') : ExampleProb P' where
  E := f Ω.E
  F := f Ω.F
  G := f Ω.G
  prob_E := by simp [hf, Ω.prob_E]
  prob_EF := by simp [hf, Ω.prob_EF, ←map_sup]
  prob_EF' := by simp [hf, Ω.prob_EF', ←map_inf]
  prob_EG := by
    rw [← map_sdiff', hf]
    exact Ω.prob_EG
  prob_G := by
    rw [← map_compl', hf]
    exact Ω.prob_G

end FinitelyAdditive
end ProbabilityTheory
