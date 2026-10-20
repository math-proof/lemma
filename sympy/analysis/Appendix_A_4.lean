import Mathlib
/-!
# Analysis I, Appendix A.4: Variables and quantifiers

Some examples of how variables and quantifiers are used in Lean

-/

namespace VariableExample1

variable (X:Type) (x y:X)
end VariableExample1

namespace VariableExample2

variable (x:ℝ)
end VariableExample2
