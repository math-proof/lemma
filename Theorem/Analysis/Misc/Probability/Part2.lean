import Mathlib
import Def.Analysis.Misc.Probability
/-! Some finite probability theory -/


namespace ProbabilityTheory

namespace FinitelyAdditive

variable {A:Type*} [BooleanAlgebra A] (P: FinitelyAdditive A)
         {A':Type*} [BooleanAlgebra A'] (P': FinitelyAdditive A')

@[simp]
theorem _root_.BoundedLatticeHom.preserves.map {f: BoundedLatticeHom A A'} (hf: f.preserves P P') (E:A) : P' (f E) = P E := hf E

end FinitelyAdditive
end ProbabilityTheory
