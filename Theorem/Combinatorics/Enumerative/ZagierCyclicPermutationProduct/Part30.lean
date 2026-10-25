/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Structure.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part5
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagOddMarkedPlane_ext {n : ℕ}
    {p q : ZagOddMarkedPlane n}
    (horder : p.order = q.order) (hvertical : p.vertical = q.vertical)
    (hroot : p.root = q.root) (hmarks : HEq p.marks q.marks) : p = q := by
  cases p
  cases q
  simp_all

theorem zagOddMarkedPlane_ext_toList {n : ℕ}
    {p q : ZagOddMarkedPlane n}
    (horder : p.order = q.order) (hvertical : p.vertical = q.vertical)
    (hroot : p.root = q.root) (hmarks : p.marks.toList = q.marks.toList) :
    p = q := by
  rcases p with ⟨e, π, r, m⟩
  rcases q with ⟨e', π', r', m'⟩
  dsimp only at horder hvertical hroot hmarks ⊢
  subst e'
  subst π'
  subst r'
  exact zagOddMarkedPlane_ext rfl rfl rfl
    (ZagOddMarks.heq_of_toList m m' hmarks)

end MetaMathlibExt
