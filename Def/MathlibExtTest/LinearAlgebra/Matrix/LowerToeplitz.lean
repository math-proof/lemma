/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/LowerToeplitz.lean -/

module

public import Mathlib.Tactic.NormNum
public import Def.LinearAlgebra.Matrix.LowerToeplitz
public import Theorem.Matrix.LowerToeplitz

@[expose] public section

/-- A concrete coefficient sequence over `ℕ` for the tests below. -/
def testSeqN : ℕ → ℕ := fun k => k + 1

/-- A concrete coefficient sequence over `ℤ` for the tests below. -/
def testSeqZ : ℕ → ℤ := fun k => (k : ℤ) + 1

