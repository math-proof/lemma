import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.LaymanCatalanHankel
open MetaMathlibExt


/--
[layman_catalan_sum_hankel_det_unrestricted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanCatalanHankel.lean)
-/
@[path]
private lemma layman_catalan_sum_hankel_det_unrestricted_eq
  {n : ℕ} :
-- imply
  Matrix.det (fun i j : Fin n =>
    ((catalan (i.val + j.val + 1) + catalan (i.val + j.val + 2) : ℕ) : ℤ)) =
    (Nat.fib (2 * n + 2) : ℤ) := by
-- proof
  apply MetaMathlibExt.layman_catalan_sum_hankel_det_unrestricted n

/--
[layman_catalan_sum_hankel_det](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanCatalanHankel.lean)
-/
@[path]
private lemma layman_catalan_sum_hankel_det_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  Matrix.det (fun i j : Fin n =>
    ((catalan (i.val + j.val + 1) + catalan (i.val + j.val + 2) : ℕ) : ℤ)) =
    (Nat.fib (2 * n + 2) : ℤ) := by
-- proof
  apply MetaMathlibExt.layman_catalan_sum_hankel_det n hn


-- created on 2026-10-20
