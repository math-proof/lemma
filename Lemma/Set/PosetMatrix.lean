import Mathlib
import sympy.Basic
import sympy.atlas.Order.PosetMatrix
open MetaMathlibExt


namespace MetaMathlibExt

/--
[IsPosetMatrix.upper](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean)
-/
@[path]
lemma IsPosetMatrix.upper
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) Bool}
-- given
  (h : IsPosetMatrix n M) :
-- imply
  ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → M i j = false :=
-- proof
  h.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsPosetMatrix.diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean)
-/
@[path]
lemma IsPosetMatrix.diagonal
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) Bool}
-- given
  (h : IsPosetMatrix n M) :
-- imply
  ∀ i : Fin n, M i i = true :=
-- proof
  h.2.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsPosetMatrix.transitive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean)
-/
@[path]
lemma IsPosetMatrix.transitive
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) Bool}
-- given
  (h : IsPosetMatrix n M) :
-- imply
  ∀ i j k : Fin n, M i j = true → M j k = true → M i k = true :=
-- proof
  h.2.2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsPosetMatrix.rel_refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean)
-/
@[path]
lemma IsPosetMatrix.rel_refl
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) Bool}
  {i : Fin n}
-- given
  (h : IsPosetMatrix n M) :
-- imply
  IsPosetMatrix.Rel M i i :=
-- proof
  h.2.1 i

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsPosetMatrix.rel_trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/PosetMatrix.lean)
-/
@[path]
lemma IsPosetMatrix.rel_trans
  {n : ℕ}
  {M : Matrix (Fin n) (Fin n) Bool}
  {i j k : Fin n}
-- given
  (h : IsPosetMatrix n M)
  (hij : IsPosetMatrix.Rel M i j)
  (hjk : IsPosetMatrix.Rel M j k) :
-- imply
  IsPosetMatrix.Rel M i k :=
-- proof
  h.2.2 i j k hij hjk

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
