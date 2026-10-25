import Mathlib
import Class.Analysis.Misc.Probability
/-! Some finite probability theory -/


namespace ProbabilityTheory

namespace FinitelyAdditive

instance instFunLike (A:Type*) [BooleanAlgebra A] :
    DFunLike (FinitelyAdditive A) A (fun _ => ℝ) :=
  { coe := fun P => P.prob
    coe_injective := by
      intro f g h
      cases f
      cases g
      congr }

end FinitelyAdditive
end ProbabilityTheory
