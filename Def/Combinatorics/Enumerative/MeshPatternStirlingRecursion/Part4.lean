/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.MeshPatternStirlingRecursion.Part2


section

namespace MetaMathlibExt

/-- The position of the maximum value of `τ : S_{t+1}`, as `τ⁻¹(last)`. -/
def maxPos (t : ℕ) (τ : Equiv.Perm (Fin (t.succ))) : Fin (t.succ) :=
  τ.symm (Fin.last t)

end MetaMathlibExt
end
