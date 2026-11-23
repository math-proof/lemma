/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanBinomialTransformHankel.lean -/

module

public import Def.Combinatorics.Enumerative.FallingKBinomialTransform
public import Theorem.Finset.Enumerative.FallingKBinomialTransform
public import Def.NumberTheory.HankelTransform
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section

/-- Binomial lower-triangular matrix with `(i, j)` entry `C(i, j)`. -/
def laymanBinomMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j => (Nat.choose i.val j.val : ℤ)

end
end MetaMathlibExt
