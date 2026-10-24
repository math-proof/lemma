import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Algebra.Polynomial.FormalOrthogonality
open MetaMathlibExt MetaMathlibExt.Polynomial


namespace MetaMathlibExt.Polynomial

/--
[not_isFormallyOrthogonal_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/FormalOrthogonality.lean)
-/
@[path]
lemma not_isFormallyOrthogonal_zero
  {R : Type*}
  [Field R] :
-- imply
  ¬ IsFormallyOrthogonal (fun _ => (0 : Polynomial R)) := by
-- proof
  intro h
  obtain ⟨_, hdeg, _, _⟩ := h
  have h1 : ((0 : Polynomial R)).natDegree = 1 := hdeg 1
  rw [Polynomial.natDegree_zero] at h1
  exact zero_ne_one h1

end MetaMathlibExt.Polynomial


-- created on 2026-10-23
