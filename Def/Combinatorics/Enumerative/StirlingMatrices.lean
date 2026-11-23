/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Matrix.Mul
public import Def.Combinatorics.Enumerative.SignedStirlingFirst
public import Theorem.Finset.Enumerative.SignedStirlingFirst
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

open BigOperators

/-!
# Stirling matrices are mutual inverses
-/

def Ssv : ℕ → ℕ → ℤ := fun n k => (Nat.stirlingSecond n k : ℤ)

def smat (N : ℕ) : Matrix (Fin N) (Fin N) ℤ := fun i j => signedStirlingFirst i.1 j.1

def Smat (N : ℕ) : Matrix (Fin N) (Fin N) ℤ := fun i j => Ssv i.1 j.1

end MetaMathlibExt
