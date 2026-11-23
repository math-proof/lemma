module

public import Mathlib
public import Theorem.Analysis.Misc.Probability

@[expose] public section

/-! Some finite probability theory -/


namespace ProbabilityTheory

namespace FinitelyAdditive

variable {A:Type*} [BooleanAlgebra A] (P: FinitelyAdditive A)
         {A':Type*} [BooleanAlgebra A'] (P': FinitelyAdditive A')

-- Some API for extending a finitely additive probability space

def _root_.BoundedLatticeHom.preserves (f: BoundedLatticeHom A A') : Prop := ∀ E:A, P' (f E) = P E

end FinitelyAdditive
end ProbabilityTheory
