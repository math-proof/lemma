import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Additive.SingerDifferenceSet
open scoped IntermediateField
open MetaMathlibExt


/--
[singer_cyclic_difference_set_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/SingerDifferenceSet.lean)
-/
@[path]
private lemma singer_cyclic_difference_set_exists_eq
  {q : ℕ}
-- given
  (hq : IsPrimePow q) :
-- imply
  ∃ D : Finset (ZMod (q ^ 2 + q + 1)), D.card = q + 1 ∧
    ∀ x : ZMod (q ^ 2 + q + 1), x ≠ 0 →
    ∃! ab : D × D, (ab.1 : ZMod (q ^ 2 + q + 1)) -
    (ab.2 : ZMod (q ^ 2 + q + 1)) = x := by
-- proof
  apply MetaMathlibExt.singer_cyclic_difference_set_exists q hq


-- created on 2026-10-20
