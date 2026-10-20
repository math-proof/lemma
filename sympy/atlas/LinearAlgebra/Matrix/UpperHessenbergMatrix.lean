/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/UpperHessenbergMatrix.lean -/

import Mathlib.Data.Matrix.Basic

/-!
# Upper Hessenberg matrices

The definition is recorded from Huilan Li and Trueman MacHenry,
*Permanents and Determinants, Weighted Isobaric Polynomials, and Integer
Sequences*, Journal of Integer Sequences 16 (2013), Article 13.3.5.
-/

namespace Matrix

/-- A square matrix is upper Hessenberg when every entry strictly below its
first subdiagonal is zero.

Stable source identifiers: concept `jis_sem_90166bc6652ac1c81120f42f`,
statement `jis_453961c69e4159797cfa575d`.
-/
def IsUpperHessenberg {n : ℕ} {R : Type*} [Zero R]
    (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j.val + 1 < i.val → M i j = 0

end Matrix
