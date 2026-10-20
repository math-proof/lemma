import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.FractalSequence
open MetaMathlibExt


/--
[FractalSequence.pos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/FractalSequence.lean)
-/
@[path]
private lemma FractalSequence_pos_injective_eq
  {X : FractalSequence}
  {i : ℕ} :
-- imply
  Function.Injective (X.pos i) := by
-- proof
  apply MetaMathlibExt.FractalSequence.pos_injective X i

/--
[FractalSequence.infinite_occurrences](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/FractalSequence.lean)
-/
@[path]
private lemma FractalSequence_infinite_occurrences_eq
  {X : FractalSequence}
  {i : ℕ} :
-- imply
  Set.Infinite {n | X.seq n = i + 1} := by
-- proof
  apply MetaMathlibExt.FractalSequence.infinite_occurrences X i


-- created on 2026-10-20
