import Mathlib
import sympy.Basic
import Def.NumberTheory.SternSequence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[stern_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SternSequence.lean)
-/
@[path]
lemma stern_zero
  :
-- imply
  sternSequence 0 = 0 := by
-- proof
  simp only [sternSequence]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[stern_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SternSequence.lean)
-/
@[path]
lemma stern_one
  :
-- imply
  sternSequence 1 = 1 := by
-- proof
  simp only [sternSequence]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[stern_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SternSequence.lean)
-/
@[path]
lemma stern_even
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  sternSequence (2 * n) = sternSequence n := by
-- proof
  have h2 : 2 * n = ((2 * n - 2) + 2) := by omega
  rw [h2]
  have hmod : (((2 * n - 2) + 2) % 2) = 0 := by omega
  have hdiv : (((2 * n - 2) + 2) / 2) = n := by omega
  simp only [sternSequence, dite_eq_left hmod, hdiv]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[stern_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SternSequence.lean)
-/
@[path]
lemma stern_odd
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  sternSequence (2 * n + 1) = sternSequence n + sternSequence (n + 1) := by
-- proof
  have h2 : 2 * n + 1 = (((2 * n + 1) - 2) + 2) := by omega
  rw [h2]
  have hne : (((2 * n + 1) - 2) + 2) % 2 ≠ 0 := by omega
  have hdiv : ((((2 * n + 1) - 2) + 2) / 2) = n := by omega
  simp only [sternSequence, dite_eq_right hne, hdiv]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
