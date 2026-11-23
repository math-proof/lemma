/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean -/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.MeshPatternStirlingRecursion.Part2

@[expose] public section

section

namespace MetaMathlibExt

/-- The position of the maximum value of `τ : S_{t+1}`, as `τ⁻¹(last)`. -/
def maxPos (t : ℕ) (τ : Equiv.Perm (Fin (t.succ))) : Fin (t.succ) :=
  τ.symm (Fin.last t)

end MetaMathlibExt
end
