import Mathlib
import Theorem.Analysis.Misc.Probability.Part2
/-! Some finite probability theory -/


namespace ProbabilityTheory

namespace FinitelyAdditive

variable {A:Type*} [BooleanAlgebra A] (P: FinitelyAdditive A)
         {A':Type*} [BooleanAlgebra A'] (P': FinitelyAdditive A')

-- an example of how a probability space can be extended while preserving various properties

class ExampleProb {A:Type*} [BooleanAlgebra A] (P: FinitelyAdditive A) where
  E : A
  F : A
  G : A
  prob_E : P E = 0.5
  prob_EF : P (E ⊔ F) = 0.75
  prob_EF' : P (E ⊓ F) = 0.25
  prob_EG : P (E \ G) = 0.4
  prob_G : P Gᶜ = 0.3

end FinitelyAdditive
end ProbabilityTheory
