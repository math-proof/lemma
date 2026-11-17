module

public import Mathlib
public import Def.LinearAlgebra.Matrix.Hankel

public section

open Matrix


namespace Matrix

/--
[hankel_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Hankel.lean)
-/
public theorem hankel_apply
  {s : ℕ → α}
  {i j : ℕ} :
-- imply
  hankel s i j = s (i + j) :=
-- proof
  rfl

end Matrix

namespace Matrix

/--
[hankelFin_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Hankel.lean)
-/
public theorem hankelFin_apply
  {n : ℕ}
  {s : ℕ → α}
  {i j : Fin n} :
-- imply
  hankelFin n s i j = s (i + j) :=
-- proof
  rfl

end Matrix


-- created on 2026-10-20
-- updated on 2026-10-26
