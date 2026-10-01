import sympy.Basic
import Mathlib.Data.Matrix.Mul


@[main]
private lemma main
  [CommRing α]
  {X : Matrix (Fin 4) (Fin 3) α}
  {Y : Matrix (Fin 3) (Fin 2) α} :
-- imply
  X * Y = Matrix.of fun i j => X i 0 * Y 0 j + X i 1 * Y 1 j + X i 2 * Y 2 j := by
-- proof
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_three]


-- created on 2021-09-21
