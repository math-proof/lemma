import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.InfiniteWord.PureMorphicWord.Part2


namespace MetaMathlibExt

/--
[doublingUnitMorphism_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/PureMorphicWord.lean)
-/
@[path]
private lemma doublingUnitMorphism_length (w : List Unit) :
  (morphExtend doublingUnitMorphism w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp [morphExtend, doublingUnitMorphism]
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[doublingUnitIterate_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/PureMorphicWord.lean)
-/
@[path]
private lemma doublingUnitIterate_length (n : Nat) :
  (morphIterate doublingUnitMorphism n [()]).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [morphIterate, doublingUnitMorphism_length, ih, pow_succ]
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[self_le_two_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/PureMorphicWord.lean)
-/
@[path]
private lemma self_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hpos : 0 < 2 ^ n := pow_pos (by omega) n
    omega

end MetaMathlibExt


-- created on 2026-10-23
