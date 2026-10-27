import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraNotes.code.Rings
open Rings


namespace Rings

/--
[zero_eq_one_of_zero_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Rings.lean)
-/
@[path]
private lemma zero_eq_one_of_zero_isUnit
  {R : Type*}
  [Ring R]
-- given
  (h : IsUnit (0 : R)) :
-- imply
  (0 : R) = 1 := by
-- proof
  obtain ⟨u, hu⟩ := h
  have h1 := u.mul_inv
  rwa [hu, zero_mul] at h1

end Rings


-- created on 2026-10-23
-- updated on 2026-10-26
