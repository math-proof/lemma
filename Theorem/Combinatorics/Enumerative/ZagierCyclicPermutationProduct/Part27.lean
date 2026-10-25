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
import Structure.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part4
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagResidualMarkedPlane_ext {n : ℕ}
    {p q : ZagResidualMarkedPlane n}
    (horder : p.order = q.order) (hvertical : p.vertical = q.vertical)
    (hmarked : HEq p.marked q.marked) (hpoint : p.point = q.point) : p = q := by
  cases p
  cases q
  simp_all

end MetaMathlibExt
