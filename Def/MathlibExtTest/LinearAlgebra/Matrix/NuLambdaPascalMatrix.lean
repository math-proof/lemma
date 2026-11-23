/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean -/

module

public import Mathlib.Tactic
public import Def.LinearAlgebra.Matrix.NuLambdaPascalMatrix
public import Theorem.Matrix.NuLambdaPascalMatrix

@[expose] public section

namespace MetaMathlibExt

def unitSkewTwo (i j : ℕ) : ℂ :=
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0

end MetaMathlibExt
