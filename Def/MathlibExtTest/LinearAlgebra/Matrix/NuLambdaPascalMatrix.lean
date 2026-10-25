/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean -/


import Mathlib.Tactic
import Def.LinearAlgebra.Matrix.NuLambdaPascalMatrix
import Lemma.Matrix.NuLambdaPascalMatrix


namespace MetaMathlibExt

def unitSkewTwo (i j : ℕ) : ℂ :=
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0

end MetaMathlibExt
