/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Misc


namespace MetaMathlibExt

variable {R : Type*} [CommRing R]

/-- Zero-based Hurwitz entry from Barry's JIS definition. -/
def hurwitzEntry (a b : ℕ → R) (i j : ℕ) : R :=
  if 2 * j + 2 ≤ i then 0
  else if i % 2 = 0 then a (j - i / 2)
  else b (j - (i - 1) / 2)

/-- Hurwitz matrix of order `n`, an `(n+1)`-by-`(n+1)` matrix.
Concept `jis_term_6793c0b8b44e37675229ccfc`, source
`https://cs.uwaterloo.ca/journals/JIS/VOL15/Barry5/barry223.tex`. -/
def hurwitzMatrix (a b : ℕ → R) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => hurwitzEntry a b i.val j.val

/-- The Hurwitz transform is the sequence of determinants of the Hurwitz matrices. -/
def hurwitzTransform (a b : ℕ → R) (n : ℕ) : R :=
  (hurwitzMatrix a b n).det

/-- Single-sequence specialization from the source, with second sequence `0 ^ n`. -/
def hurwitzSingle (a : ℕ → R) (n : ℕ) : R :=
  hurwitzTransform a (fun k => (0 : R) ^ k) n

end MetaMathlibExt
