import Mathlib
import sympy.Basic
import sympy.atlas.Order.PosetMatrix
open MetaMathlibExt


/--
[IsPosetMatrix.upper](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean)
-/
@[path]
private lemma IsPosetMatrix_upper_eq
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) Bool}
-- given
  (h : IsPosetMatrix n M) :
-- imply
  ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → M i j = false := by
-- proof
  apply MetaMathlibExt.IsPosetMatrix.upper h

/--
[IsPosetMatrix.diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean)
-/
@[path]
private lemma IsPosetMatrix_diagonal_eq
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) Bool}
-- given
  (h : IsPosetMatrix n M) :
-- imply
  ∀ i : Fin n, M i i = true := by
-- proof
  apply MetaMathlibExt.IsPosetMatrix.diagonal h

/--
[IsPosetMatrix.transitive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean)
-/
@[path]
private lemma IsPosetMatrix_transitive_eq
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) Bool}
-- given
  (h : IsPosetMatrix n M) :
-- imply
  ∀ i j k : Fin n, M i j = true → M j k = true → M i k = true := by
-- proof
  apply MetaMathlibExt.IsPosetMatrix.transitive h

/--
[IsPosetMatrix.rel_refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean)
-/
@[path]
private lemma IsPosetMatrix_rel_refl_eq
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) Bool}
  {i : Fin n}
-- given
  (h : IsPosetMatrix n M) :
-- imply
  IsPosetMatrix.Rel M i i := by
-- proof
  apply MetaMathlibExt.IsPosetMatrix.rel_refl h i

/--
[IsPosetMatrix.rel_trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean)
-/
@[path]
private lemma IsPosetMatrix_rel_trans_eq
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) Bool}
  {i j k : Fin n}
-- given
  (h : IsPosetMatrix n M)
  (hij : IsPosetMatrix.Rel M i j)
  (hjk : IsPosetMatrix.Rel M j k) :
-- imply
  IsPosetMatrix.Rel M i k := by
-- proof
  apply MetaMathlibExt.IsPosetMatrix.rel_trans h i j k hij hjk


-- created on 2026-10-20
