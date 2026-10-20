import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.BellPermutationsSecondKind
open MetaMathlibExt


/--
[bell_perm_second_kind_weakExcedance_eq_stirlingSecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma bell_perm_second_kind_weakExcedance_eq_stirlingSecond_eq
  {n k : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  let IsRGF : (Fin n → Fin n) → Prop := by
-- proof
  apply MetaMathlibExt.bell_perm_second_kind_weakExcedance_eq_stirlingSecond n k hn


-- created on 2026-10-20
