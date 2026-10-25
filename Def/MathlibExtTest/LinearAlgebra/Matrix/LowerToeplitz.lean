/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/LowerToeplitz.lean -/


import Mathlib.Tactic.NormNum
import Def.LinearAlgebra.Matrix.LowerToeplitz
import Lemma.Matrix.LowerToeplitz


/-- A concrete coefficient sequence over `ℕ` for the tests below. -/
def testSeqN : ℕ → ℕ := fun k => k + 1

/-- A concrete coefficient sequence over `ℤ` for the tests below. -/
def testSeqZ : ℕ → ℤ := fun k => (k : ℤ) + 1

