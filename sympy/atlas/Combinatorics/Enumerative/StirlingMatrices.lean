/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Matrix.Mul
import sympy.atlas.Combinatorics.Enumerative.SignedStirlingFirst
import Lemma.Finset.Enumerative.SignedStirlingFirst
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

open BigOperators

/-!
# Stirling matrices are mutual inverses
-/

private def Ssv : ℕ → ℕ → ℤ := fun n k => (Nat.stirlingSecond n k : ℤ)

private def smat (N : ℕ) : Matrix (Fin N) (Fin N) ℤ := fun i j => signedStirlingFirst i.1 j.1
private def Smat (N : ℕ) : Matrix (Fin N) (Fin N) ℤ := fun i j => Ssv i.1 j.1
end MetaMathlibExt
