/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/EulerSeidelMatrix.lean -/


import sympy.atlas.Combinatorics.Enumerative.EulerSeidelMatrix
import Lemma.Finset.Enumerative.EulerSeidelMatrix

namespace MetaMathlibExt

example : eulerSeidelMatrix (fun n : ℕ => n) 2 0 = 2 := by rfl
example : eulerSeidelMatrix (fun n : ℕ => n) 2 2 = 12 := by rfl
example : eulerSeidelMatrix (fun n : ℕ => n) 0 2 = 4 := by
  rw [eulerSeidelMatrix_eq_sum]
  rfl

end MetaMathlibExt
