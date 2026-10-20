import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.AlmostBeattyPartition
open MetaMathlibExt


/--
[beattyTerm_eq_floor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AlmostBeattyPartition.lean)
-/
@[path]
private lemma beattyTerm_eq_floor_eq
  {n : { n : ℕ // 0 < n }}
  {α : ℝ} :
-- imply
  beattyTerm n α = Nat.floor ((n.val : ℝ) / α) := by
-- proof
  apply MetaMathlibExt.beattyTerm_eq_floor n α

/--
[beattyTerm_isAlmostBeattySequence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AlmostBeattyPartition.lean)
-/
@[path]
private lemma beattyTerm_isAlmostBeattySequence_eq
  {α : ℝ}
-- given
  (hα0 : 0 < α)
  (hα1 : α < 1) :
-- imply
  IsAlmostBeattySequence (fun n => beattyTerm n α) α := by
-- proof
  apply MetaMathlibExt.beattyTerm_isAlmostBeattySequence α hα0 hα1


-- created on 2026-10-20
