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

theorem hurwitzEntry_eq_zero_of_le (a b : ℕ → R) {i j : ℕ}
    (h : 2 * j + 2 ≤ i) : hurwitzEntry a b i j = 0 := by
  simp [hurwitzEntry, h]

theorem hurwitzEntry_of_even (a b : ℕ → R) {i j : ℕ}
    (h : ¬2 * j + 2 ≤ i) (he : i % 2 = 0) :
    hurwitzEntry a b i j = a (j - i / 2) := by
  simp [hurwitzEntry, h, he]

theorem hurwitzEntry_of_odd (a b : ℕ → R) {i j : ℕ}
    (h : ¬2 * j + 2 ≤ i) (ho : i % 2 ≠ 0) :
    hurwitzEntry a b i j = b (j - (i - 1) / 2) := by
  simp [hurwitzEntry, h, ho]

theorem hurwitz_half_le_of_even {i j : ℕ}
    (h : ¬2 * j + 2 ≤ i) (he : i % 2 = 0) : i / 2 ≤ j := by
  omega

theorem hurwitz_pred_half_le_of_odd {i j : ℕ}
    (h : ¬2 * j + 2 ≤ i) (_ho : i % 2 ≠ 0) : (i - 1) / 2 ≤ j := by
  omega

theorem hurwitzTransform_zero (a b : ℕ → R) :
    hurwitzTransform a b 0 = a 0 := by
  unfold hurwitzTransform hurwitzMatrix
  rw [Matrix.det_fin_one]
  simp [Matrix.of_apply, hurwitzEntry]

theorem hurwitzTransform_one (a b : ℕ → R) :
    hurwitzTransform a b 1 = a 0 * b 1 - a 1 * b 0 := by
  unfold hurwitzTransform hurwitzMatrix
  rw [Matrix.det_fin_two]
  simp [Matrix.of_apply, hurwitzEntry]

end MetaMathlibExt
