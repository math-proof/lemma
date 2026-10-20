/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/LowerToeplitz.lean -/

import Mathlib.Data.Matrix.Basic

namespace Matrix

/-- Lower-triangular Toeplitz matrix over `ℕ × ℕ`: given a sequence `a`,
the `(i, j)` entry is `a (i - j)` when `j ≤ i`, and `0` otherwise. In
particular the matrix is constant on each subdiagonal and vanishes strictly
above the main diagonal.

Source: Ming-Jian Ding and Jiang Zeng, "Some New Results on the Minuscule
Polynomials of Type A," Journal of Integer Sequences 28 (2025), lines 640-653.
URL: `https://cs.uwaterloo.ca/journals/JIS/VOL28/Zeng/zeng26.tex`.
Full TeX SHA-256:
`2a5a8d59641da82808dae4aea4c6583f460dd36bc175d9dce912a265a5ce7a1a`.
Exact source-span SHA-256 including terminal LF:
`63b54ec23b76494d198b28837c6622e4bbe92e064580f13cde8f3d1523ac28e3`.
Grounded concept: `jis_grounded_6e7ca1c0ec8f4d9d675959b3`. -/
def lowerToeplitz {R : Type*} [Zero R] (a : ℕ → R) : Matrix ℕ ℕ R :=
  fun i j => if j ≤ i then a (i - j) else 0

/-- Below-diagonal (and diagonal) entries of a lower-triangular Toeplitz matrix. -/
@[simp]
theorem lowerToeplitz_apply_of_le {R : Type*} [Zero R] (a : ℕ → R) {i j : ℕ}
    (h : j ≤ i) : lowerToeplitz a i j = a (i - j) := by
  simp [lowerToeplitz, h]

/-- Above-diagonal entries of a lower-triangular Toeplitz matrix vanish. -/
@[simp]
theorem lowerToeplitz_apply_of_gt {R : Type*} [Zero R] (a : ℕ → R) {i j : ℕ}
    (h : i < j) : lowerToeplitz a i j = 0 := by
  simp [lowerToeplitz, Nat.not_le.mpr h]

/-- Diagonal entries of a lower-triangular Toeplitz matrix equal `a 0`. -/
@[simp]
theorem lowerToeplitz_apply_diag {R : Type*} [Zero R] (a : ℕ → R) (i : ℕ) :
    lowerToeplitz a i i = a 0 := by
  have h : i ≤ i := Nat.le_refl i
  rw [lowerToeplitz_apply_of_le a h, Nat.sub_self]

end Matrix
