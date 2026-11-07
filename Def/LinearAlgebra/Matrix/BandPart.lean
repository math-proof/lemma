import Mathlib.Data.Matrix.Basic


/--
Dilated band, matching [tf.linalg.band_part](https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part)
and `Tensor.band_part`.

Entry `(i, j)` is kept when `(j : ℤ) - (i : ℤ)` lies in `Icc (-l) u` and `d` divides that
difference plus `l`; every other entry is `0`. `d = 1` is the undilated band.
-/
def Matrix.band_part {m n : ℕ} {α : Type*} [Zero α]
    (X : Matrix (Fin m) (Fin n) α) (l u : ℕ) (d : ℕ := 1) : Matrix (Fin m) (Fin n) α :=
  Matrix.of fun i j =>
    let Δ : ℤ := (j : ℤ) - (i : ℤ)
    if -((l : ℤ)) ≤ Δ ∧ Δ ≤ u ∧ (d : ℤ) ∣ Δ + l then
      X i j
    else
      0
