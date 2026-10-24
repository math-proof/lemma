import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedSylvester
open Nat


namespace Nat

/--
[generalizedSylvester_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedSylvester.lean)
-/
@[path]
lemma generalizedSylvester_zero
  {n : ℕ} :
-- imply
  generalizedSylvester n 0 = n + 1 :=
-- proof
  rfl

end Nat

namespace Nat

/--
[generalizedSylvester_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedSylvester.lean)
-/
@[path]
lemma generalizedSylvester_succ
  {n k : ℕ} :
-- imply
  generalizedSylvester n (k + 1) =
      generalizedSylvester n k ^ 2 - generalizedSylvester n k + 1 :=
-- proof
  rfl

end Nat

namespace Nat

/--
[generalizedSylvester_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedSylvester.lean)
-/
@[path]
lemma generalizedSylvester_pos
  {n k : ℕ} :
-- imply
  0 < generalizedSylvester n k := by
-- proof
  cases k <;> simp

end Nat


-- created on 2026-10-20
-- updated on 2026-10-23
