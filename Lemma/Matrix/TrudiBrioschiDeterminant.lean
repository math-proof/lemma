import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.TrudiBrioschiDeterminant
open MetaMathlibExt


/--
[Matrix.det_toeplitzHessenberg_eq_sum_compositions_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma Matrix_det_toeplitzHessenberg_eq_sum_compositions_general_eq
  [CommRing R]
  {n : Nat}
  {a : Nat → R} :
-- imply
  Matrix.det (fun i j : Fin n =>
    if (j : Nat) ≤ (i : Nat) + 1 then a ((i : Nat) + 1 - (j : Nat)) else 0) =
    Finset.univ.sum (fun c : Composition n =>
    (-a 0) ^ (n - c.length) *
    Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r))) := by
-- proof
  apply MetaMathlibExt.Matrix.det_toeplitzHessenberg_eq_sum_compositions_general n a

/--
[Matrix.det_toeplitzHessenberg_eq_sum_compositions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/TrudiBrioschiDeterminant.lean)
-/
@[path]
private lemma Matrix_det_toeplitzHessenberg_eq_sum_compositions_eq
  [CommRing R]
  {n : Nat}
  {a : Nat → R}
-- given
  (hn : 0 < n)
  (ha0 : a 0 ≠ 0) :
-- imply
  Matrix.det (fun i j : Fin n =>
    if (j : Nat) ≤ (i : Nat) + 1 then a ((i : Nat) + 1 - (j : Nat)) else 0) =
    Finset.univ.sum (fun c : Composition n =>
    (-a 0) ^ (n - c.length) *
    Finset.univ.prod (fun r : Fin c.length => a (c.blocksFun r))) := by
-- proof
  apply MetaMathlibExt.Matrix.det_toeplitzHessenberg_eq_sum_compositions n hn a ha0


-- created on 2026-10-20
