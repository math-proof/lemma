/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanBinomialTransformHankel.lean -/

import Def.Combinatorics.Enumerative.FallingKBinomialTransform
import Lemma.Finset.Enumerative.FallingKBinomialTransform
import Def.NumberTheory.HankelTransform
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

section

/-- Binomial lower-triangular matrix with `(i, j)` entry `C(i, j)`. -/
def laymanBinomMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j => (Nat.choose i.val j.val : ℤ)

end
end MetaMathlibExt
